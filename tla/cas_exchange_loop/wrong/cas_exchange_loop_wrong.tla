------------------------- MODULE cas_exchange_loop_wrong--------------------

(***************************************************************************

WARNING: THIS VERSION IS FOR THE WRONG IMPLEMENTATION FROM THE PRESENTATION.
IT IS HERE TO CHECK THAT THE TLA+ INVARIANTS AND TLC MODEL IS WORKING CORRECTLY.
PLEASE REFER TO cas_exchange_loop.tla FOR THE ACTUAL ALGORITHM SPECIFICATION.

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

1. No memory leak occurs.
2. No torn read occurs on the fast path.
3. No use after free
4. No data race occurs.

NOTE: IN THIS BROKEN MODEL, WE CAN'T SEE THE MEMORY LEAK, TORN READ, OR DATA RACE.
ASSERTS WILL CATCH THE USE AFTER FREE PROBLEM DUE TO THE ABA PROBLEM.

 ***************************************************************************)

EXTENDS Sequences, Integers, TLC

(***************************************************************************
This defines the maximum limit of the memory in the model.

For modeling purposes, this should be above 2 as the algorithm should have
at most two objects allocated at a time.
 ***************************************************************************)
CONSTANT kMemoryCapacity

(***************************************************************************
An Object is something we store in the memory. Each object consists of multiple
ObjectElements, as we need to model torn writes/reads.

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
This is a default constructed object to initialize the storage as per the
original algorithm. We simply choose an arbitrary object of kObjectSize.
It doesn't matter what the make up of the object is as it shouldn't be read.
 ***************************************************************************)
DefaultObject == [i \in 1..kObjectSize |-> UninitializedElement]

(* --algorithm cas_exchange_loop

variables
    g_memory = [i \in 1..kMemoryCapacity |-> IF i = 1 THEN DefaultObject ELSE EMPTY], \* Need to model the memory allocation
    g_storage_pointer = 1,   \* storage in the original
    g_in_use = FALSE;        \* isInAudioThread in the original

process reader = "reader"
variables
    reader_local_pointer,  \* coeff in the original
    read_index = 1, \* Used to model reading through the data in multiple steps.
    local_data = DefaultObject;
begin
    ReaderSetInUseTrue:
        g_in_use := TRUE;

    ReaderReadPointer:
        reader_local_pointer := g_storage_pointer;
    
    ReaderCopyObject:
        while read_index <= kObjectSize do
            assert g_memory[reader_local_pointer] # EMPTY;
            local_data[read_index] := g_memory[reader_local_pointer][read_index];
            ReaderReadObjectInc:
                read_index := read_index + 1;
        end while;

    ReaderSetInUseFalse:
        g_in_use := FALSE;
end process;

process writer = "writer"
variables
    writer_local_pointer, \* ptr in original
    chosen_element,       \* A shortcut variable to choose a single element from ObjectElements so it is stationary in the write loop. May be replaced with `with`?
    write_index = 1;      \* Used to model writing through the data in multiple steps.
begin
    \* We first start by finding a free slot in memory and allocate the memory
    \* with a default initialized object.
    \*
    \* If this CHOOSE ever fails, it means we have run out of memory and likely
    \* there was a memory leak. 
    WriterAllocateObject:
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
            assert g_memory[writer_local_pointer] # EMPTY;
            g_memory[writer_local_pointer][write_index] := chosen_element;
            WriterWriteObjectLoopInc:
                write_index := write_index + 1;
        end while;

    WriterWaitForNotInUse:
        await g_in_use = FALSE;

    WriterSwapPointer:
        writer_local_pointer := g_storage_pointer || g_storage_pointer := writer_local_pointer;

    WriterDeletePointer:
        assert g_memory[writer_local_pointer] # EMPTY;
        g_memory[writer_local_pointer] := EMPTY;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "18aa7fde" /\ chksum(tla) = "c8185e08")
CONSTANT defaultInitValue
VARIABLES g_memory, g_storage_pointer, g_in_use, pc, reader_local_pointer, 
          read_index, local_data, writer_local_pointer, chosen_element, 
          write_index

vars == << g_memory, g_storage_pointer, g_in_use, pc, reader_local_pointer, 
           read_index, local_data, writer_local_pointer, chosen_element, 
           write_index >>

ProcSet == {"reader"} \cup {"writer"}

Init == (* Global variables *)
        /\ g_memory = [i \in 1..kMemoryCapacity |-> IF i = 1 THEN DefaultObject ELSE EMPTY]
        /\ g_storage_pointer = 1
        /\ g_in_use = FALSE
        (* Process reader *)
        /\ reader_local_pointer = defaultInitValue
        /\ read_index = 1
        /\ local_data = DefaultObject
        (* Process writer *)
        /\ writer_local_pointer = defaultInitValue
        /\ chosen_element = defaultInitValue
        /\ write_index = 0
        /\ pc = [self \in ProcSet |-> CASE self = "reader" -> "ReaderSetInUseTrue"
                                        [] self = "writer" -> "WriterAllocateObject"]

ReaderSetInUseTrue == /\ pc["reader"] = "ReaderSetInUseTrue"
                      /\ g_in_use' = TRUE
                      /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadPointer"]
                      /\ UNCHANGED << g_memory, g_storage_pointer, 
                                      reader_local_pointer, read_index, 
                                      local_data, writer_local_pointer, 
                                      chosen_element, write_index >>

ReaderReadPointer == /\ pc["reader"] = "ReaderReadPointer"
                     /\ reader_local_pointer' = g_storage_pointer
                     /\ pc' = [pc EXCEPT !["reader"] = "ReaderCopyObject"]
                     /\ UNCHANGED << g_memory, g_storage_pointer, g_in_use, 
                                     read_index, local_data, 
                                     writer_local_pointer, chosen_element, 
                                     write_index >>

ReaderCopyObject == /\ pc["reader"] = "ReaderCopyObject"
                    /\ IF read_index <= kObjectSize
                          THEN /\ Assert(g_memory[reader_local_pointer] # EMPTY, 
                                         "Failure of assertion at line 109, column 13.")
                               /\ local_data' = [local_data EXCEPT ![read_index] = g_memory[reader_local_pointer][read_index]]
                               /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadObjectInc"]
                          ELSE /\ pc' = [pc EXCEPT !["reader"] = "ReaderSetInUseFalse"]
                               /\ UNCHANGED local_data
                    /\ UNCHANGED << g_memory, g_storage_pointer, g_in_use, 
                                    reader_local_pointer, read_index, 
                                    writer_local_pointer, chosen_element, 
                                    write_index >>

ReaderReadObjectInc == /\ pc["reader"] = "ReaderReadObjectInc"
                       /\ read_index' = read_index + 1
                       /\ pc' = [pc EXCEPT !["reader"] = "ReaderCopyObject"]
                       /\ UNCHANGED << g_memory, g_storage_pointer, g_in_use, 
                                       reader_local_pointer, local_data, 
                                       writer_local_pointer, chosen_element, 
                                       write_index >>

ReaderSetInUseFalse == /\ pc["reader"] = "ReaderSetInUseFalse"
                       /\ g_in_use' = FALSE
                       /\ pc' = [pc EXCEPT !["reader"] = "Done"]
                       /\ UNCHANGED << g_memory, g_storage_pointer, 
                                       reader_local_pointer, read_index, 
                                       local_data, writer_local_pointer, 
                                       chosen_element, write_index >>

reader == ReaderSetInUseTrue \/ ReaderReadPointer \/ ReaderCopyObject
             \/ ReaderReadObjectInc \/ ReaderSetInUseFalse

WriterAllocateObject == /\ pc["writer"] = "WriterAllocateObject"
                        /\ writer_local_pointer' = (CHOOSE i \in DOMAIN g_memory: g_memory[i] = EMPTY)
                        /\ g_memory' = [g_memory EXCEPT ![writer_local_pointer'] = DefaultObject]
                        /\ pc' = [pc EXCEPT !["writer"] = "WriterChooseObjectElement"]
                        /\ UNCHANGED << g_storage_pointer, g_in_use, 
                                        reader_local_pointer, read_index, 
                                        local_data, chosen_element, 
                                        write_index >>

WriterChooseObjectElement == /\ pc["writer"] = "WriterChooseObjectElement"
                             /\ \E elem \in ObjectElements:
                                  chosen_element' = elem
                             /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteObject"]
                             /\ UNCHANGED << g_memory, g_storage_pointer, 
                                             g_in_use, reader_local_pointer, 
                                             read_index, local_data, 
                                             writer_local_pointer, write_index >>

WriterWriteObject == /\ pc["writer"] = "WriterWriteObject"
                     /\ IF write_index <= kObjectSize
                           THEN /\ Assert(g_memory[writer_local_pointer] # EMPTY, 
                                          "Failure of assertion at line 156, column 13.")
                                /\ g_memory' = [g_memory EXCEPT ![writer_local_pointer][write_index] = chosen_element]
                                /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteObjectLoopInc"]
                           ELSE /\ pc' = [pc EXCEPT !["writer"] = "WriterWaitForNotInUse"]
                                /\ UNCHANGED g_memory
                     /\ UNCHANGED << g_storage_pointer, g_in_use, 
                                     reader_local_pointer, read_index, 
                                     local_data, writer_local_pointer, 
                                     chosen_element, write_index >>

WriterWriteObjectLoopInc == /\ pc["writer"] = "WriterWriteObjectLoopInc"
                            /\ write_index' = write_index + 1
                            /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteObject"]
                            /\ UNCHANGED << g_memory, g_storage_pointer, 
                                            g_in_use, reader_local_pointer, 
                                            read_index, local_data, 
                                            writer_local_pointer, 
                                            chosen_element >>

WriterWaitForNotInUse == /\ pc["writer"] = "WriterWaitForNotInUse"
                         /\ g_in_use = FALSE
                         /\ pc' = [pc EXCEPT !["writer"] = "WriterSwapPointer"]
                         /\ UNCHANGED << g_memory, g_storage_pointer, g_in_use, 
                                         reader_local_pointer, read_index, 
                                         local_data, writer_local_pointer, 
                                         chosen_element, write_index >>

WriterSwapPointer == /\ pc["writer"] = "WriterSwapPointer"
                     /\ /\ g_storage_pointer' = writer_local_pointer
                        /\ writer_local_pointer' = g_storage_pointer
                     /\ pc' = [pc EXCEPT !["writer"] = "WriterDeletePointer"]
                     /\ UNCHANGED << g_memory, g_in_use, reader_local_pointer, 
                                     read_index, local_data, chosen_element, 
                                     write_index >>

WriterDeletePointer == /\ pc["writer"] = "WriterDeletePointer"
                       /\ Assert(g_memory[writer_local_pointer] # EMPTY, 
                                 "Failure of assertion at line 169, column 9.")
                       /\ g_memory' = [g_memory EXCEPT ![writer_local_pointer] = EMPTY]
                       /\ pc' = [pc EXCEPT !["writer"] = "Done"]
                       /\ UNCHANGED << g_storage_pointer, g_in_use, 
                                       reader_local_pointer, read_index, 
                                       local_data, writer_local_pointer, 
                                       chosen_element, write_index >>

writer == WriterAllocateObject \/ WriterChooseObjectElement
             \/ WriterWriteObject \/ WriterWriteObjectLoopInc
             \/ WriterWaitForNotInUse \/ WriterSwapPointer
             \/ WriterDeletePointer

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reader \/ writer
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat Mar 23 13:21:24 EDT 2024 by shuhao
\* Created Sat Mar 23 11:26:21 EDT 2024 by shuhao
