-------------------------- MODULE CASExchangeLoop --------------------------

EXTENDS Integers, FiniteSets, Sequences

\* Maximum capacity of memory available to the algorithm
CONSTANT kMemoryCapacity

\* A (model) value representing uninitialized memory.
CONSTANT kUninitialized

\* The number of iterations the RT loop is allowed to run. When the RT loop
\* terminates, the specification forces the termination of the non-RT loop so
\* TLC does not check forever.
CONSTANT kNumOfRTIterations

(*--algorithm CASExchangeLoop
variables
  \* Initialize memory array. Set the first element to a valid value and every 
  \* else to be uninitialized.
  \*
  \* Valid values in the memory array are integers, which represents arbitrary
  \* objects in a real programming language. If it is kUninitialied, then the
  \* memory has not been allocated.
  \*
  \* The CASExchange algorithm is all about swapping pointers in real life. In
  \* TLA+, this is represented via indices.
  Memory = [i \in 1..kMemoryCapacity |-> IF i = 1 THEN 1 ELSE kUninitialized],
  \* Used as a workaround to detect data race. Data race is only checked on the
  \* Memory variable as all other variables do not have problems with data
  \* races.
  \* See this thread for details: http://discuss.tlapl.us/msg04894.html
  MemoryAccessCounter = [i \in 1..kMemoryCapacity |-> [reads |-> 0, writes |-> 0]],
  \* PlusCal procedures cannot directly return variables. A global variable is needed.
  \* Since we only call Malloc/Read from a single thread, we can get away with a
  \* single variable, otherwise we would need a function with the domain = ProcSet.
  NewPointer,     \* Return value for  Malloc
  MemoryRead = 0, \* Return value for ReadMemory
  \* This is the atomic<Data*> that is getting swapped. It corresponds to
  \* the biquadCoeff variable from the farbot presentation (slide 45).
  AtomicDataPointer = 1,
  \* This is the global owner of the data, which in code would be an
  \* unique_ptr<Data>. It corresponds to the storage variable from the farbot
  \* presentation (slide 45).
  StorageDataPointer = 1,
  \* This is an artificial variable to ensure the algorithm terminates.
  \* TODO: maybe this is not needed and we still can assert useful stuff, but
  \* I'm not sure how to do it. Alternatively, could use State Constraints?
  Stopped = FALSE;

macro CompareAndSwap(expectedValue, newValue, valueRef, swapped) begin
  if (valueRef = expectedValue) then
    valueRef := newValue;
    swapped := TRUE;
  else
    swapped := FALSE;
  end if;
end macro;

\* This version of compare and swap is incorrectly implemented. 
\* Comment it in to observe the effects.
\*macro CompareAndSwap(expectedValue, newValue, valueRef, swapped) begin
\*  valueRef := newValue;
\*  swapped := TRUE;
\*end macro;

procedure Malloc() begin
  malloc1:
    \* Find a free slot of memory. If we run out of memory, obviously that is bad
    \* as the algorithm should have bounded memory usage.
    NewPointer := CHOOSE i \in DOMAIN Memory : Memory[i] = kUninitialized;
  
    \* Just need to set it to any value that's not kUninitialized for the spec to
    \* recognize it as a valid object.
    Memory[NewPointer] := NewPointer;

    MemoryAccessCounter[NewPointer].writes := MemoryAccessCounter[NewPointer].writes + 1;
  malloc2:
    MemoryAccessCounter[NewPointer].writes := MemoryAccessCounter[NewPointer].writes - 1;
    return;
end procedure;

procedure Free(pointer) begin
  free1:
    Memory[pointer] := kUninitialized;
    MemoryAccessCounter[pointer].writes := MemoryAccessCounter[pointer].writes + 1;
  free2:
    MemoryAccessCounter[pointer].writes := MemoryAccessCounter[pointer].writes - 1;
    return;
end procedure;

procedure ReadMemory(pointer) begin
  readmem1:
    MemoryRead := Memory[pointer];
    MemoryAccessCounter[pointer].reads := MemoryAccessCounter[pointer].reads + 1;
  readmem2:
    MemoryAccessCounter[pointer].reads := MemoryAccessCounter[pointer].reads - 1;
    return;
end procedure;

fair process NonRtThread = "NonRtThread"
  variables
    expectedPointer,  \* Holds the expected pointer during the CAS loop.
    swapped,          \* A boolean indicating whether or not the CAS was successful.
    nonRTLoopIdx = 0; \* Needed to ensure TLC doesn't loop forever.
begin
  non_rt_loop:
    while (Stopped = FALSE) do
      nonRTLoopIdx := nonRTLoopIdx + 1; \* Non-essential part of the spec to make it work with TLC.
      swapped := FALSE; \* Technically, this variable should be pushed into the stack every loop, so we have to reset it every loop.
      non_rt_new:
        call Malloc();
      non_rt_cas_loop:
        while (swapped = FALSE) do
          non_rt_cas_read:
            \* In C++, compare_exchange_strong will update the value of expected
            \* if it fails. However, in the reference code, this behavior is
            \* "forced" off as the for loop reads the expected from storage 
            \* every iteration. This is why the following line of code is needed.
            expectedPointer := StorageDataPointer;
          non_rt_cas_cas:
            CompareAndSwap(expectedPointer, NewPointer, AtomicDataPointer, swapped);
        end while;
        \* At this point, the original AtomicDataPointer should have taken the 
        \* value of the newly allocated newDataPointer. The StorageDataPointer
        \* is unchanged for now, and the ownership resides with the local
        \* variable newDataPointer, which is about to be deleted as it goes out
        \* of scope. The reference implementation then does 
        \* OwnedDataPointer = std::move(newDataPointer), which is captured in
        \* the next two steps. This ensures the old data is cleaned up and the 
        \* data is properly owned (by a global variable).
      non_rt_delete:
        \* Is the order correct? Does unique_ptr delete first then reassign? 
        \* Certainly easier to write in TLA if true.
        \* TODO: maybe it doesn't even matter. This can be confirmed by swapping
        \* these two steps and rerunning TLC.
        call Free(StorageDataPointer);
      non_rt_move_ptr:
        StorageDataPointer := NewPointer;
    end while;
end process;

fair process RtThread = "RtThread"
  variables
    rtLocalPointer, \* The pointer read by the RT thread.
    rtLoopIdx = 0,  \* Needed to ensure TLC doesn't loop forever.
begin
  rt_loop:
    while (rtLoopIdx < kNumOfRTIterations) do
      rtLoopIdx := rtLoopIdx + 1;
      rt_exchange:
        \* Atomically exchange the AtomicDataPointer with a "null" value to
        \* signal to the non-RT thread that it is busy with the data and
        \* shouldn't be changed while it is busy.
        rtLocalPointer := AtomicDataPointer || AtomicDataPointer := 0;
      rt_use_data:
        call ReadMemory(rtLocalPointer);
      rt_exchange_back:
        AtomicDataPointer := rtLocalPointer;
    end while;
end process;

end algorithm*)
\* BEGIN TRANSLATION (chksum(pcal) = "a29d5d6b" /\ chksum(tla) = "cc482faf")
\* Parameter pointer of procedure Free at line 82 col 16 changed to pointer_
CONSTANT defaultInitValue
VARIABLES Memory, MemoryAccessCounter, NewPointer, MemoryRead, 
          AtomicDataPointer, StorageDataPointer, Stopped, pc, stack, pointer_, 
          pointer, expectedPointer, swapped, nonRTLoopIdx, rtLocalPointer, 
          rtLoopIdx

vars == << Memory, MemoryAccessCounter, NewPointer, MemoryRead, 
           AtomicDataPointer, StorageDataPointer, Stopped, pc, stack, 
           pointer_, pointer, expectedPointer, swapped, nonRTLoopIdx, 
           rtLocalPointer, rtLoopIdx >>

ProcSet == {"NonRtThread"} \cup {"RtThread"}

Init == (* Global variables *)
        /\ Memory = [i \in 1..kMemoryCapacity |-> IF i = 1 THEN 1 ELSE kUninitialized]
        /\ MemoryAccessCounter = [i \in 1..kMemoryCapacity |-> [reads |-> 0, writes |-> 0]]
        /\ NewPointer = defaultInitValue
        /\ MemoryRead = 0
        /\ AtomicDataPointer = 1
        /\ StorageDataPointer = 1
        /\ Stopped = FALSE
        (* Procedure Free *)
        /\ pointer_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ReadMemory *)
        /\ pointer = [ self \in ProcSet |-> defaultInitValue]
        (* Process NonRtThread *)
        /\ expectedPointer = defaultInitValue
        /\ swapped = defaultInitValue
        /\ nonRTLoopIdx = 0
        (* Process RtThread *)
        /\ rtLocalPointer = defaultInitValue
        /\ rtLoopIdx = 0
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "NonRtThread" -> "non_rt_loop"
                                        [] self = "RtThread" -> "rt_loop"]

malloc1(self) == /\ pc[self] = "malloc1"
                 /\ NewPointer' = (CHOOSE i \in DOMAIN Memory : Memory[i] = kUninitialized)
                 /\ Memory' = [Memory EXCEPT ![NewPointer'] = NewPointer']
                 /\ MemoryAccessCounter' = [MemoryAccessCounter EXCEPT ![NewPointer'].writes = MemoryAccessCounter[NewPointer'].writes + 1]
                 /\ pc' = [pc EXCEPT ![self] = "malloc2"]
                 /\ UNCHANGED << MemoryRead, AtomicDataPointer, 
                                 StorageDataPointer, Stopped, stack, pointer_, 
                                 pointer, expectedPointer, swapped, 
                                 nonRTLoopIdx, rtLocalPointer, rtLoopIdx >>

malloc2(self) == /\ pc[self] = "malloc2"
                 /\ MemoryAccessCounter' = [MemoryAccessCounter EXCEPT ![NewPointer].writes = MemoryAccessCounter[NewPointer].writes - 1]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << Memory, NewPointer, MemoryRead, 
                                 AtomicDataPointer, StorageDataPointer, 
                                 Stopped, pointer_, pointer, expectedPointer, 
                                 swapped, nonRTLoopIdx, rtLocalPointer, 
                                 rtLoopIdx >>

Malloc(self) == malloc1(self) \/ malloc2(self)

free1(self) == /\ pc[self] = "free1"
               /\ Memory' = [Memory EXCEPT ![pointer_[self]] = kUninitialized]
               /\ MemoryAccessCounter' = [MemoryAccessCounter EXCEPT ![pointer_[self]].writes = MemoryAccessCounter[pointer_[self]].writes + 1]
               /\ pc' = [pc EXCEPT ![self] = "free2"]
               /\ UNCHANGED << NewPointer, MemoryRead, AtomicDataPointer, 
                               StorageDataPointer, Stopped, stack, pointer_, 
                               pointer, expectedPointer, swapped, nonRTLoopIdx, 
                               rtLocalPointer, rtLoopIdx >>

free2(self) == /\ pc[self] = "free2"
               /\ MemoryAccessCounter' = [MemoryAccessCounter EXCEPT ![pointer_[self]].writes = MemoryAccessCounter[pointer_[self]].writes - 1]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ pointer_' = [pointer_ EXCEPT ![self] = Head(stack[self]).pointer_]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Memory, NewPointer, MemoryRead, 
                               AtomicDataPointer, StorageDataPointer, Stopped, 
                               pointer, expectedPointer, swapped, nonRTLoopIdx, 
                               rtLocalPointer, rtLoopIdx >>

Free(self) == free1(self) \/ free2(self)

readmem1(self) == /\ pc[self] = "readmem1"
                  /\ MemoryRead' = Memory[pointer[self]]
                  /\ MemoryAccessCounter' = [MemoryAccessCounter EXCEPT ![pointer[self]].reads = MemoryAccessCounter[pointer[self]].reads + 1]
                  /\ pc' = [pc EXCEPT ![self] = "readmem2"]
                  /\ UNCHANGED << Memory, NewPointer, AtomicDataPointer, 
                                  StorageDataPointer, Stopped, stack, pointer_, 
                                  pointer, expectedPointer, swapped, 
                                  nonRTLoopIdx, rtLocalPointer, rtLoopIdx >>

readmem2(self) == /\ pc[self] = "readmem2"
                  /\ MemoryAccessCounter' = [MemoryAccessCounter EXCEPT ![pointer[self]].reads = MemoryAccessCounter[pointer[self]].reads - 1]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ pointer' = [pointer EXCEPT ![self] = Head(stack[self]).pointer]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << Memory, NewPointer, MemoryRead, 
                                  AtomicDataPointer, StorageDataPointer, 
                                  Stopped, pointer_, expectedPointer, swapped, 
                                  nonRTLoopIdx, rtLocalPointer, rtLoopIdx >>

ReadMemory(self) == readmem1(self) \/ readmem2(self)

non_rt_loop == /\ pc["NonRtThread"] = "non_rt_loop"
               /\ IF (Stopped = FALSE)
                     THEN /\ nonRTLoopIdx' = nonRTLoopIdx + 1
                          /\ swapped' = FALSE
                          /\ pc' = [pc EXCEPT !["NonRtThread"] = "non_rt_new"]
                     ELSE /\ pc' = [pc EXCEPT !["NonRtThread"] = "Done"]
                          /\ UNCHANGED << swapped, nonRTLoopIdx >>
               /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                               MemoryRead, AtomicDataPointer, 
                               StorageDataPointer, Stopped, stack, pointer_, 
                               pointer, expectedPointer, rtLocalPointer, 
                               rtLoopIdx >>

non_rt_new == /\ pc["NonRtThread"] = "non_rt_new"
              /\ stack' = [stack EXCEPT !["NonRtThread"] = << [ procedure |->  "Malloc",
                                                                pc        |->  "non_rt_cas_loop" ] >>
                                                            \o stack["NonRtThread"]]
              /\ pc' = [pc EXCEPT !["NonRtThread"] = "malloc1"]
              /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                              MemoryRead, AtomicDataPointer, 
                              StorageDataPointer, Stopped, pointer_, pointer, 
                              expectedPointer, swapped, nonRTLoopIdx, 
                              rtLocalPointer, rtLoopIdx >>

non_rt_cas_loop == /\ pc["NonRtThread"] = "non_rt_cas_loop"
                   /\ IF (swapped = FALSE)
                         THEN /\ pc' = [pc EXCEPT !["NonRtThread"] = "non_rt_cas_read"]
                         ELSE /\ pc' = [pc EXCEPT !["NonRtThread"] = "non_rt_delete"]
                   /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                                   MemoryRead, AtomicDataPointer, 
                                   StorageDataPointer, Stopped, stack, 
                                   pointer_, pointer, expectedPointer, swapped, 
                                   nonRTLoopIdx, rtLocalPointer, rtLoopIdx >>

non_rt_cas_read == /\ pc["NonRtThread"] = "non_rt_cas_read"
                   /\ expectedPointer' = StorageDataPointer
                   /\ pc' = [pc EXCEPT !["NonRtThread"] = "non_rt_cas_cas"]
                   /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                                   MemoryRead, AtomicDataPointer, 
                                   StorageDataPointer, Stopped, stack, 
                                   pointer_, pointer, swapped, nonRTLoopIdx, 
                                   rtLocalPointer, rtLoopIdx >>

non_rt_cas_cas == /\ pc["NonRtThread"] = "non_rt_cas_cas"
                  /\ IF (AtomicDataPointer = expectedPointer)
                        THEN /\ AtomicDataPointer' = NewPointer
                             /\ swapped' = TRUE
                        ELSE /\ swapped' = FALSE
                             /\ UNCHANGED AtomicDataPointer
                  /\ pc' = [pc EXCEPT !["NonRtThread"] = "non_rt_cas_loop"]
                  /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                                  MemoryRead, StorageDataPointer, Stopped, 
                                  stack, pointer_, pointer, expectedPointer, 
                                  nonRTLoopIdx, rtLocalPointer, rtLoopIdx >>

non_rt_delete == /\ pc["NonRtThread"] = "non_rt_delete"
                 /\ /\ pointer_' = [pointer_ EXCEPT !["NonRtThread"] = StorageDataPointer]
                    /\ stack' = [stack EXCEPT !["NonRtThread"] = << [ procedure |->  "Free",
                                                                      pc        |->  "non_rt_move_ptr",
                                                                      pointer_  |->  pointer_["NonRtThread"] ] >>
                                                                  \o stack["NonRtThread"]]
                 /\ pc' = [pc EXCEPT !["NonRtThread"] = "free1"]
                 /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                                 MemoryRead, AtomicDataPointer, 
                                 StorageDataPointer, Stopped, pointer, 
                                 expectedPointer, swapped, nonRTLoopIdx, 
                                 rtLocalPointer, rtLoopIdx >>

non_rt_move_ptr == /\ pc["NonRtThread"] = "non_rt_move_ptr"
                   /\ StorageDataPointer' = NewPointer
                   /\ pc' = [pc EXCEPT !["NonRtThread"] = "non_rt_loop"]
                   /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                                   MemoryRead, AtomicDataPointer, Stopped, 
                                   stack, pointer_, pointer, expectedPointer, 
                                   swapped, nonRTLoopIdx, rtLocalPointer, 
                                   rtLoopIdx >>

NonRtThread == non_rt_loop \/ non_rt_new \/ non_rt_cas_loop
                  \/ non_rt_cas_read \/ non_rt_cas_cas \/ non_rt_delete
                  \/ non_rt_move_ptr

rt_loop == /\ pc["RtThread"] = "rt_loop"
           /\ IF (rtLoopIdx < kNumOfRTIterations)
                 THEN /\ rtLoopIdx' = rtLoopIdx + 1
                      /\ pc' = [pc EXCEPT !["RtThread"] = "rt_exchange"]
                 ELSE /\ pc' = [pc EXCEPT !["RtThread"] = "Done"]
                      /\ UNCHANGED rtLoopIdx
           /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, MemoryRead, 
                           AtomicDataPointer, StorageDataPointer, Stopped, 
                           stack, pointer_, pointer, expectedPointer, swapped, 
                           nonRTLoopIdx, rtLocalPointer >>

rt_exchange == /\ pc["RtThread"] = "rt_exchange"
               /\ /\ AtomicDataPointer' = 0
                  /\ rtLocalPointer' = AtomicDataPointer
               /\ pc' = [pc EXCEPT !["RtThread"] = "rt_use_data"]
               /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                               MemoryRead, StorageDataPointer, Stopped, stack, 
                               pointer_, pointer, expectedPointer, swapped, 
                               nonRTLoopIdx, rtLoopIdx >>

rt_use_data == /\ pc["RtThread"] = "rt_use_data"
               /\ /\ pointer' = [pointer EXCEPT !["RtThread"] = rtLocalPointer]
                  /\ stack' = [stack EXCEPT !["RtThread"] = << [ procedure |->  "ReadMemory",
                                                                 pc        |->  "rt_exchange_back",
                                                                 pointer   |->  pointer["RtThread"] ] >>
                                                             \o stack["RtThread"]]
               /\ pc' = [pc EXCEPT !["RtThread"] = "readmem1"]
               /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                               MemoryRead, AtomicDataPointer, 
                               StorageDataPointer, Stopped, pointer_, 
                               expectedPointer, swapped, nonRTLoopIdx, 
                               rtLocalPointer, rtLoopIdx >>

rt_exchange_back == /\ pc["RtThread"] = "rt_exchange_back"
                    /\ AtomicDataPointer' = rtLocalPointer
                    /\ pc' = [pc EXCEPT !["RtThread"] = "rt_loop"]
                    /\ UNCHANGED << Memory, MemoryAccessCounter, NewPointer, 
                                    MemoryRead, StorageDataPointer, Stopped, 
                                    stack, pointer_, pointer, expectedPointer, 
                                    swapped, nonRTLoopIdx, rtLocalPointer, 
                                    rtLoopIdx >>

RtThread == rt_loop \/ rt_exchange \/ rt_use_data \/ rt_exchange_back

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == NonRtThread \/ RtThread
           \/ (\E self \in ProcSet:  \/ Malloc(self) \/ Free(self)
                                     \/ ReadMemory(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(NonRtThread)
           /\ WF_vars(Malloc("NonRtThread"))
           /\ WF_vars(Free("NonRtThread"))
        /\ WF_vars(RtThread) /\ WF_vars(ReadMemory("RtThread"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MemoryUsage == Cardinality({i \in DOMAIN Memory : Memory[i] # kUninitialized})

ActionConstraintNonRTThreadDoesNotInfinitelySpin ==
  (nonRTLoopIdx - rtLoopIdx) < 3

(*************************************
 Invariants and temporal conditions
 ==================================

 Invariants

 - Ensure no access to uninitialized memory
 - Ensure no memory leak (memory usage remains bounded)
 - Ensure no data race on Memory
   - AtomicDataPointer cannot have a data race because it is an atomic type in implementation?
   - StorageDataPointer cannot have a data race because only the non-RT loop read and write to it.
   - Memory can have data race on access and on malloc/free.

 Temporal conditions

 - Ensure that data is eventually swapped and the data is eventually read.
 - Ensure that past data is not read

 *************************************)

WriteDataRace == \E i \in DOMAIN MemoryAccessCounter: MemoryAccessCounter[i].writes > 1
ReadDataRace == \E i \in DOMAIN MemoryAccessCounter: MemoryAccessCounter[i].writes >= 1 /\ MemoryAccessCounter[i].reads >= 1

InvariantNoUninitializedMemoryAccess == MemoryRead # kUninitialized
InvariantNoMemoryLeak == MemoryUsage <= 2
InvariantNoWriteDataRace == ~WriteDataRace
InvariantNoReadDataRace == ~ReadDataRace


=============================================================================
\* Modification History
\* Last modified Sat Jun 04 18:21:31 EDT 2022 by shuhao
\* Created Fri May 27 15:43:27 EDT 2022 by shuhao
