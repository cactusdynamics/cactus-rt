------------------------- MODULE cas_exchange_loop -------------------------

(***************************************************************************

This algorithm was originally introduced by Dave Rowland and Fabien Renn-Giles
in  Real-time 101 - Part II: The real-time audio developer's toolbox
(https://youtu.be/PoZAo2Vikbo?t=297).

The original idea for this algorithm is for the writer to be on the slow
(non-real-time) path and reader to be on the fast (real-time) path.

The idea is to use an atomic pointer and a heap-allocated object that's always
tracked. The atomic pointer will point to nullptr if the fast-path reader is
currently reading the value. Otherwise, it will point to the heap-allocated
object (or an older version of the heap-allocated object). Effectively, this is
using the nullptr as an "in-use" flag for this atomic pointer. The tracked
heap-allocated object stores the "latest" object.

The slow-path reader allocates a new object and CAS the atomic pointer if the
atomic pointer is currently not null. If it is successfuly, it has exchanged
the pointer to the new object with the pointer to the previous iteration of the
object. The slow-path then updates the tracked heap-allocated object to be
the new object, while deleting the previous object to avoid a memory leak.

This algorithm is able to send an object of any size to the fast thread without
copying. It requires memory allocation and deallocation on the slow-path. The
fast-path is wait-free while the slow-path is lock-free (if memory allocation
is lock-free). This supports at most one reader and one writer.

The goal of this specification is to write the above down and check for the
following properties:

1. No memory leak occurs (InvariantNoMemoryLeak)
2. No torn read occurs on the fast path (assertions in reader process)
3. No use after free (assertions in readers and writers)
4. No data race occurs (TODO. Is this necessary given that we already have
   multiple step writing and data race detection? Also see 
   https://groups.google.com/g/tlaplus/c/2uum_SHipJ0/m/jf04a9p7AwAJ)
5. The data is passed from the writer to the reader successfully at the end
   (assertion in the reader, specifically the ReaderStorePtr, and manually
   checked by producing a counter example. See: 
   https://groups.google.com/g/tlaplus/c/gVdl99UIkLU/m/aMkOQhieAQAJ.
   TODO: Figure out a better way).

This model only specifies a single iteration of the CAS exchange loop as
described. As a result, it starts from a valid starting state. The spec then
goes on to describe a single writer/reader iteration in any arbitrary order.
This means it is possible for the writer to occur after the reader. This makes
the 5th property above (temporal property) difficult to write. It may be
possible to constrain it such that the writer does not run if the reader already
finished. That said, it's not really easy to define when the "reader is finished"
without missing some cases, so it's left here as is.

 ***************************************************************************)

EXTENDS Sequences, Integers, TLC, FiniteSets

(***************************************************************************
This defines the maximum limit of the memory in the model.

For modeling purposes, this should be above 2 as the algorithm should have
at most two objects allocated at a time.
 ***************************************************************************)
CONSTANT kMemoryCapacity

(***************************************************************************
An Object is something we store in the memory. Each object consists of multiple
ObjectElements, as we need to model torn writes/reads. Each object also consists
of the same ObjectElements, to more easily detect torn reads.

For modeling purposes, these should be model values like {e0, e1}. Two
elements is likely enough.
 ***************************************************************************)
CONSTANT ObjectElements

(***************************************************************************
This is the size of the object. Each object has kObjectSize ObjectElements.

For modeling, it must be greater than 1.
 ***************************************************************************)
CONSTANT kObjectSize

(***************************************************************************
NULLPTR: A null pointer
EMPTY: A marker showing the memory slot is empty
 ***************************************************************************)
CONSTANTS NULLPTR, EMPTY

(***************************************************************************
An uninitialized object element.
 ***************************************************************************)
UninitializedElement == CHOOSE e: e \notin ObjectElements

(***************************************************************************
Ways to create objects. Objects are sequences of multiple of the
same ObjectElements.
 ***************************************************************************)
ObjectWithValue(value) == [i \in 1..kObjectSize |-> value]
DefaultObject == ObjectWithValue(UninitializedElement)

\* Pick a random object element for the initial state. Could theoretically make
\* the initial be different objects.
InitialObject == ObjectWithValue(CHOOSE e \in ObjectElements: TRUE)

(* --algorithm cas_exchange_loop

variables
    g_storage_pointer \in 1..kMemoryCapacity,   \* storage in the original
    g_memory = [i \in 1..kMemoryCapacity |-> IF i = g_storage_pointer THEN InitialObject ELSE EMPTY], \* Need to model the memory allocation
    g_atomic_pointer = g_storage_pointer,    \* biquadCoeff in the original
    g_writer_written_data_for_assertion = EMPTY; \* We atomically use TLA+ to write to this variable, so we can do an equality assertion to make sure we read the right data.

define
    MemoryUsage == Cardinality({i \in 1..kMemoryCapacity: g_memory[i] # EMPTY})
    InvariantNoMemoryLeak == MemoryUsage <= 2

    DataIsNotTorn(data) == Cardinality({data[i] : i \in 1..kObjectSize}) = 1
end define;

fair process reader = "reader"
variables
    reader_local_pointer,  \* coeff in the original
    read_index = 1,        \* Used to model reading through the data in multiple steps.
    reader_local_data = DefaultObject;
begin
    ReaderExchangePtr:
        assert g_atomic_pointer # NULLPTR; \* Assert that the atomic pointer is not null when we start. i.e. the writer didn't write nullptr
        reader_local_pointer := g_atomic_pointer;
        g_atomic_pointer := NULLPTR;

    ReaderCopyObject:
        while read_index <= kObjectSize do
            assert g_memory[reader_local_pointer] # EMPTY; \* Asserts no read to an invalid pointer
            assert DataIsNotTorn(g_memory[reader_local_pointer]); \* Assert the write wasn't torn when this read occurs
            reader_local_data[read_index] := g_memory[reader_local_pointer][read_index];
            ReaderReadObjectInc:
                read_index := read_index + 1;
        end while;

    ReaderStorePtr:
        assert DataIsNotTorn(reader_local_data); \* Assert the read data is not torn when we read it
        \* Either the read happened before the write and the g_writer_written_data_for_assertion is empty.
        \* Or the write happened before the read and we have g_writer_written_data_for_assertion as the intended write.
        \* In which case we assert that the read data is indeed what was written.
        \* Thereby we confirmed that the data written by the writer was properly transmitted to the reader.
        \* We need to use a temporal property to to ensure that the second branch of this \/ condition happens.
        assert \/ g_writer_written_data_for_assertion = EMPTY
               \/ g_writer_written_data_for_assertion = reader_local_data;
        g_atomic_pointer := reader_local_pointer;
end process;

fair process writer = "writer"
variables
    writer_local_pointer, \* newBiquad in original
    chosen_element,       \* A shortcut variable to choose a single element from ObjectElements so it is stationary in the write loop. May be replaced with `with`?
    writer_expected_ptr,  \* expected in the origin
    exchanged = FALSE,    \* A variable to indicate if the exchange is successful.
    write_index = 1;      \* Used to model writing through the data in multiple steps.
begin
    \* We first start by finding a free slot in memory and allocate the memory
    \* with a default initialized object.
    \*
    \* If this CHOOSE ever fails, it means we have run out of memory and likely
    \* there was a memory leak.
    WriterAllocateObject:
        assert Cardinality({i \in DOMAIN g_memory : g_memory[i] = EMPTY}) > 0; \* Check OOM

        writer_local_pointer := CHOOSE i \in DOMAIN g_memory: g_memory[i] = EMPTY;

        \* Assign a default object.
        g_memory[writer_local_pointer] := DefaultObject;


    \* In this specification, we always write the same object element value to
    \* the object. This makes it easy to check if a torn read/write occured
    \* as the invariant for that simply becomes whether or not the number of
    \* unique object values is 1 or not in an object.
    \*
    \* Maybe this is not the best way to choose an element as it introduces yet
    \* another step. However, I'm not sure how to fix it.
    \* TODO: fix this.
    WriterChooseObjectElement:
        with elem \in ObjectElements do
            chosen_element := elem;
        end with;

    \* In this specification, we need to model the data write, to make sure
    \* that writes here doesn't actually affect the reads. This is similar to
    \* the copy constructor that's called when the original code's
    \* changeBiquadParameters is called.
    WriterWriteObject:
        while write_index <= kObjectSize do
            assert g_memory[writer_local_pointer] # EMPTY; \* Check use after free
            g_memory[writer_local_pointer][write_index] := chosen_element;
            WriterWriteObjectLoopInc:
                write_index := write_index + 1;
        end while;

    WriterCASLoop:
        while exchanged = FALSE do
            writer_expected_ptr := g_storage_pointer;
            WriterCASCAS:
                if (writer_expected_ptr = g_atomic_pointer) then
                    g_atomic_pointer := writer_local_pointer || writer_local_pointer := g_atomic_pointer;
                    g_writer_written_data_for_assertion := ObjectWithValue(chosen_element); \* Not a part of the algorithm. Not implementable in real-life. Used for assertion instead.
                    exchanged := TRUE;
                end if;
        end while;

    WriterUpdateStoragePointer:
        g_storage_pointer := writer_local_pointer;

    WriterDeleteOldData:
        assert g_memory[writer_local_pointer] # EMPTY; \* Check double free
        g_memory[writer_local_pointer] := EMPTY;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "68798429" /\ chksum(tla) = "d128285c")
CONSTANT defaultInitValue
VARIABLES g_storage_pointer, g_memory, g_atomic_pointer, 
          g_writer_written_data_for_assertion, pc

(* define statement *)
MemoryUsage == Cardinality({i \in 1..kMemoryCapacity: g_memory[i] # EMPTY})
InvariantNoMemoryLeak == MemoryUsage <= 2

DataIsNotTorn(data) == Cardinality({data[i] : i \in 1..kObjectSize}) = 1

VARIABLES reader_local_pointer, read_index, reader_local_data, 
          writer_local_pointer, chosen_element, writer_expected_ptr, 
          exchanged, write_index

vars == << g_storage_pointer, g_memory, g_atomic_pointer, 
           g_writer_written_data_for_assertion, pc, reader_local_pointer, 
           read_index, reader_local_data, writer_local_pointer, 
           chosen_element, writer_expected_ptr, exchanged, write_index >>

ProcSet == {"reader"} \cup {"writer"}

Init == (* Global variables *)
        /\ g_storage_pointer \in 1..kMemoryCapacity
        /\ g_memory = [i \in 1..kMemoryCapacity |-> IF i = g_storage_pointer THEN InitialObject ELSE EMPTY]
        /\ g_atomic_pointer = g_storage_pointer
        /\ g_writer_written_data_for_assertion = EMPTY
        (* Process reader *)
        /\ reader_local_pointer = defaultInitValue
        /\ read_index = 1
        /\ reader_local_data = DefaultObject
        (* Process writer *)
        /\ writer_local_pointer = defaultInitValue
        /\ chosen_element = defaultInitValue
        /\ writer_expected_ptr = defaultInitValue
        /\ exchanged = FALSE
        /\ write_index = 1
        /\ pc = [self \in ProcSet |-> CASE self = "reader" -> "ReaderExchangePtr"
                                        [] self = "writer" -> "WriterAllocateObject"]

ReaderExchangePtr == /\ pc["reader"] = "ReaderExchangePtr"
                     /\ Assert(g_atomic_pointer # NULLPTR, 
                               "Failure of assertion at line 127, column 9.")
                     /\ reader_local_pointer' = g_atomic_pointer
                     /\ g_atomic_pointer' = NULLPTR
                     /\ pc' = [pc EXCEPT !["reader"] = "ReaderCopyObject"]
                     /\ UNCHANGED << g_storage_pointer, g_memory, 
                                     g_writer_written_data_for_assertion, 
                                     read_index, reader_local_data, 
                                     writer_local_pointer, chosen_element, 
                                     writer_expected_ptr, exchanged, 
                                     write_index >>

ReaderCopyObject == /\ pc["reader"] = "ReaderCopyObject"
                    /\ IF read_index <= kObjectSize
                          THEN /\ Assert(g_memory[reader_local_pointer] # EMPTY, 
                                         "Failure of assertion at line 133, column 13.")
                               /\ Assert(DataIsNotTorn(g_memory[reader_local_pointer]), 
                                         "Failure of assertion at line 134, column 13.")
                               /\ reader_local_data' = [reader_local_data EXCEPT ![read_index] = g_memory[reader_local_pointer][read_index]]
                               /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadObjectInc"]
                          ELSE /\ pc' = [pc EXCEPT !["reader"] = "ReaderStorePtr"]
                               /\ UNCHANGED reader_local_data
                    /\ UNCHANGED << g_storage_pointer, g_memory, 
                                    g_atomic_pointer, 
                                    g_writer_written_data_for_assertion, 
                                    reader_local_pointer, read_index, 
                                    writer_local_pointer, chosen_element, 
                                    writer_expected_ptr, exchanged, 
                                    write_index >>

ReaderReadObjectInc == /\ pc["reader"] = "ReaderReadObjectInc"
                       /\ read_index' = read_index + 1
                       /\ pc' = [pc EXCEPT !["reader"] = "ReaderCopyObject"]
                       /\ UNCHANGED << g_storage_pointer, g_memory, 
                                       g_atomic_pointer, 
                                       g_writer_written_data_for_assertion, 
                                       reader_local_pointer, reader_local_data, 
                                       writer_local_pointer, chosen_element, 
                                       writer_expected_ptr, exchanged, 
                                       write_index >>

ReaderStorePtr == /\ pc["reader"] = "ReaderStorePtr"
                  /\ Assert(DataIsNotTorn(reader_local_data), 
                            "Failure of assertion at line 141, column 9.")
                  /\ Assert(\/ g_writer_written_data_for_assertion = EMPTY
                            \/ g_writer_written_data_for_assertion = reader_local_data, 
                            "Failure of assertion at line 147, column 9.")
                  /\ g_atomic_pointer' = reader_local_pointer
                  /\ pc' = [pc EXCEPT !["reader"] = "Done"]
                  /\ UNCHANGED << g_storage_pointer, g_memory, 
                                  g_writer_written_data_for_assertion, 
                                  reader_local_pointer, read_index, 
                                  reader_local_data, writer_local_pointer, 
                                  chosen_element, writer_expected_ptr, 
                                  exchanged, write_index >>

reader == ReaderExchangePtr \/ ReaderCopyObject \/ ReaderReadObjectInc
             \/ ReaderStorePtr

WriterAllocateObject == /\ pc["writer"] = "WriterAllocateObject"
                        /\ Assert(Cardinality({i \in DOMAIN g_memory : g_memory[i] = EMPTY}) > 0, 
                                  "Failure of assertion at line 166, column 9.")
                        /\ writer_local_pointer' = (CHOOSE i \in DOMAIN g_memory: g_memory[i] = EMPTY)
                        /\ g_memory' = [g_memory EXCEPT ![writer_local_pointer'] = DefaultObject]
                        /\ pc' = [pc EXCEPT !["writer"] = "WriterChooseObjectElement"]
                        /\ UNCHANGED << g_storage_pointer, g_atomic_pointer, 
                                        g_writer_written_data_for_assertion, 
                                        reader_local_pointer, read_index, 
                                        reader_local_data, chosen_element, 
                                        writer_expected_ptr, exchanged, 
                                        write_index >>

WriterChooseObjectElement == /\ pc["writer"] = "WriterChooseObjectElement"
                             /\ \E elem \in ObjectElements:
                                  chosen_element' = elem
                             /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteObject"]
                             /\ UNCHANGED << g_storage_pointer, g_memory, 
                                             g_atomic_pointer, 
                                             g_writer_written_data_for_assertion, 
                                             reader_local_pointer, read_index, 
                                             reader_local_data, 
                                             writer_local_pointer, 
                                             writer_expected_ptr, exchanged, 
                                             write_index >>

WriterWriteObject == /\ pc["writer"] = "WriterWriteObject"
                     /\ IF write_index <= kObjectSize
                           THEN /\ Assert(g_memory[writer_local_pointer] # EMPTY, 
                                          "Failure of assertion at line 193, column 13.")
                                /\ g_memory' = [g_memory EXCEPT ![writer_local_pointer][write_index] = chosen_element]
                                /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteObjectLoopInc"]
                           ELSE /\ pc' = [pc EXCEPT !["writer"] = "WriterCASLoop"]
                                /\ UNCHANGED g_memory
                     /\ UNCHANGED << g_storage_pointer, g_atomic_pointer, 
                                     g_writer_written_data_for_assertion, 
                                     reader_local_pointer, read_index, 
                                     reader_local_data, writer_local_pointer, 
                                     chosen_element, writer_expected_ptr, 
                                     exchanged, write_index >>

WriterWriteObjectLoopInc == /\ pc["writer"] = "WriterWriteObjectLoopInc"
                            /\ write_index' = write_index + 1
                            /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteObject"]
                            /\ UNCHANGED << g_storage_pointer, g_memory, 
                                            g_atomic_pointer, 
                                            g_writer_written_data_for_assertion, 
                                            reader_local_pointer, read_index, 
                                            reader_local_data, 
                                            writer_local_pointer, 
                                            chosen_element, 
                                            writer_expected_ptr, exchanged >>

WriterCASLoop == /\ pc["writer"] = "WriterCASLoop"
                 /\ IF exchanged = FALSE
                       THEN /\ writer_expected_ptr' = g_storage_pointer
                            /\ pc' = [pc EXCEPT !["writer"] = "WriterCASCAS"]
                       ELSE /\ pc' = [pc EXCEPT !["writer"] = "WriterUpdateStoragePointer"]
                            /\ UNCHANGED writer_expected_ptr
                 /\ UNCHANGED << g_storage_pointer, g_memory, g_atomic_pointer, 
                                 g_writer_written_data_for_assertion, 
                                 reader_local_pointer, read_index, 
                                 reader_local_data, writer_local_pointer, 
                                 chosen_element, exchanged, write_index >>

WriterCASCAS == /\ pc["writer"] = "WriterCASCAS"
                /\ IF (writer_expected_ptr = g_atomic_pointer)
                      THEN /\ /\ g_atomic_pointer' = writer_local_pointer
                              /\ writer_local_pointer' = g_atomic_pointer
                           /\ g_writer_written_data_for_assertion' = ObjectWithValue(chosen_element)
                           /\ exchanged' = TRUE
                      ELSE /\ TRUE
                           /\ UNCHANGED << g_atomic_pointer, 
                                           g_writer_written_data_for_assertion, 
                                           writer_local_pointer, exchanged >>
                /\ pc' = [pc EXCEPT !["writer"] = "WriterCASLoop"]
                /\ UNCHANGED << g_storage_pointer, g_memory, 
                                reader_local_pointer, read_index, 
                                reader_local_data, chosen_element, 
                                writer_expected_ptr, write_index >>

WriterUpdateStoragePointer == /\ pc["writer"] = "WriterUpdateStoragePointer"
                              /\ g_storage_pointer' = writer_local_pointer
                              /\ pc' = [pc EXCEPT !["writer"] = "WriterDeleteOldData"]
                              /\ UNCHANGED << g_memory, g_atomic_pointer, 
                                              g_writer_written_data_for_assertion, 
                                              reader_local_pointer, read_index, 
                                              reader_local_data, 
                                              writer_local_pointer, 
                                              chosen_element, 
                                              writer_expected_ptr, exchanged, 
                                              write_index >>

WriterDeleteOldData == /\ pc["writer"] = "WriterDeleteOldData"
                       /\ Assert(g_memory[writer_local_pointer] # EMPTY, 
                                 "Failure of assertion at line 214, column 9.")
                       /\ g_memory' = [g_memory EXCEPT ![writer_local_pointer] = EMPTY]
                       /\ pc' = [pc EXCEPT !["writer"] = "Done"]
                       /\ UNCHANGED << g_storage_pointer, g_atomic_pointer, 
                                       g_writer_written_data_for_assertion, 
                                       reader_local_pointer, read_index, 
                                       reader_local_data, writer_local_pointer, 
                                       chosen_element, writer_expected_ptr, 
                                       exchanged, write_index >>

writer == WriterAllocateObject \/ WriterChooseObjectElement
             \/ WriterWriteObject \/ WriterWriteObjectLoopInc
             \/ WriterCASLoop \/ WriterCASCAS \/ WriterUpdateStoragePointer
             \/ WriterDeleteOldData

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reader \/ writer
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(reader)
        /\ WF_vars(writer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Mar 29 10:07:45 EDT 2024 by shuhao
\* Created Sat Mar 23 11:26:21 EDT 2024 by shuhao
