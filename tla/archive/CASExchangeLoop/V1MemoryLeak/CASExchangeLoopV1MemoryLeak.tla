---- MODULE CASExchangeLoopV1MemoryLeak ----
EXTENDS TLC, Integers, Sequences, FiniteSets

\* Maximum capacity of Memory
CONSTANT MemoryCapacity

\* A (model) value representing that a memory location is uninitialized 
CONSTANT Uninitialized

\* Number of iterations for the RT loop to run.
\* When the RT loop terminates, it also terminates the non-RT loop.
\* Action constraints in TLC should prevent the non-RT loop from infinitely 
\* spinning.
CONSTANT RTIterations

(*--algorithm CASExchangeLoop
variables 
  \* Initialize the memory to be uninitialized except the first entry
  Memory = [i \in 1..MemoryCapacity |-> IF i = 1 THEN 1 ELSE Uninitialized],

  \* Initialize the pointer to a valid memory location
  DataPointer = 1,

  \* Set to TRUE once the non-RT loop exits.
  Stopped = FALSE;

fair process NonRTThread = "NonRTThread"
  variables
    nonRTLocalDataPointer, 
    nonRTLoopIdx = 0; \* Needed for the action constraint
begin
  non_rt_loop:
    while (Stopped # TRUE) do
      nonRTLoopIdx := nonRTLoopIdx + 1;
      non_rt_new:
        nonRTLocalDataPointer := CHOOSE i \in DOMAIN Memory : Memory[i] = Uninitialized;
        Memory[nonRTLocalDataPointer] := nonRTLocalDataPointer;
      non_rt_assign:
        DataPointer := nonRTLocalDataPointer;
    end while;
end process;

fair process RTThread = "RTThread"
variables
  rtLocalDataPointer,
  rtLoopIdx = 0;
begin
  rt_loop:
    while (rtLoopIdx < RTIterations) do
      rtLoopIdx := rtLoopIdx + 1;
      rt_load:
        rtLocalDataPointer := DataPointer;
      rt_proc:
        \* skip;
        assert Memory[rtLocalDataPointer] # Uninitialized;
    end while;
    Stopped := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b0f59b38" /\ chksum(tla) = "fee14d5a")
CONSTANT defaultInitValue
VARIABLES Memory, DataPointer, Stopped, pc, nonRTLocalDataPointer, 
          nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx

vars == << Memory, DataPointer, Stopped, pc, nonRTLocalDataPointer, 
           nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx >>

ProcSet == {"NonRTThread"} \cup {"RTThread"}

Init == (* Global variables *)
        /\ Memory = [i \in 1..MemoryCapacity |-> IF i = 1 THEN 1 ELSE Uninitialized]
        /\ DataPointer = 1
        /\ Stopped = FALSE
        (* Process NonRTThread *)
        /\ nonRTLocalDataPointer = defaultInitValue
        /\ nonRTLoopIdx = 0
        (* Process RTThread *)
        /\ rtLocalDataPointer = defaultInitValue
        /\ rtLoopIdx = 0
        /\ pc = [self \in ProcSet |-> CASE self = "NonRTThread" -> "non_rt_loop"
                                        [] self = "RTThread" -> "rt_loop"]

non_rt_loop == /\ pc["NonRTThread"] = "non_rt_loop"
               /\ IF (Stopped # TRUE)
                     THEN /\ nonRTLoopIdx' = nonRTLoopIdx + 1
                          /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_new"]
                     ELSE /\ pc' = [pc EXCEPT !["NonRTThread"] = "Done"]
                          /\ UNCHANGED nonRTLoopIdx
               /\ UNCHANGED << Memory, DataPointer, Stopped, 
                               nonRTLocalDataPointer, rtLocalDataPointer, 
                               rtLoopIdx >>

non_rt_new == /\ pc["NonRTThread"] = "non_rt_new"
              /\ nonRTLocalDataPointer' = (CHOOSE i \in DOMAIN Memory : Memory[i] = Uninitialized)
              /\ Memory' = [Memory EXCEPT ![nonRTLocalDataPointer'] = nonRTLocalDataPointer']
              /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_assign"]
              /\ UNCHANGED << DataPointer, Stopped, nonRTLoopIdx, 
                              rtLocalDataPointer, rtLoopIdx >>

non_rt_assign == /\ pc["NonRTThread"] = "non_rt_assign"
                 /\ DataPointer' = nonRTLocalDataPointer
                 /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_loop"]
                 /\ UNCHANGED << Memory, Stopped, nonRTLocalDataPointer, 
                                 nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx >>

NonRTThread == non_rt_loop \/ non_rt_new \/ non_rt_assign

rt_loop == /\ pc["RTThread"] = "rt_loop"
           /\ IF (rtLoopIdx < RTIterations)
                 THEN /\ rtLoopIdx' = rtLoopIdx + 1
                      /\ pc' = [pc EXCEPT !["RTThread"] = "rt_load"]
                      /\ UNCHANGED Stopped
                 ELSE /\ Stopped' = TRUE
                      /\ pc' = [pc EXCEPT !["RTThread"] = "Done"]
                      /\ UNCHANGED rtLoopIdx
           /\ UNCHANGED << Memory, DataPointer, nonRTLocalDataPointer, 
                           nonRTLoopIdx, rtLocalDataPointer >>

rt_load == /\ pc["RTThread"] = "rt_load"
           /\ rtLocalDataPointer' = DataPointer
           /\ pc' = [pc EXCEPT !["RTThread"] = "rt_proc"]
           /\ UNCHANGED << Memory, DataPointer, Stopped, nonRTLocalDataPointer, 
                           nonRTLoopIdx, rtLoopIdx >>

rt_proc == /\ pc["RTThread"] = "rt_proc"
           /\ Assert(Memory[rtLocalDataPointer] # Uninitialized, 
                     "Failure of assertion at line 55, column 9.")
           /\ pc' = [pc EXCEPT !["RTThread"] = "rt_loop"]
           /\ UNCHANGED << Memory, DataPointer, Stopped, nonRTLocalDataPointer, 
                           nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx >>

RTThread == rt_loop \/ rt_load \/ rt_proc

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == NonRTThread \/ RTThread
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(NonRTThread)
        /\ WF_vars(RTThread)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MemoryUsage ==
  Cardinality({i \in DOMAIN Memory : Memory[i] # Uninitialized})

\* An action constraint that constrains the NonRT thread from infinitely 
\* spinning. Currently hard coded so it cannot be 3 loop iterations ahead.
ActionConstraintNonRTThreadDoesNotInfinitelySpin ==
  (nonRTLoopIdx - rtLoopIdx) < 3

\* Makes sure the RT thread never accesses uninitialized memory.
InvariantNoUninitializedMemoryAccess ==
  (pc["RTThread"] = "rt_proc") => (Memory[rtLocalDataPointer] # Uninitialized)

\* Makes sure we don't use an infinite amount of memory
InvariantNoMemoryLeak ==
  MemoryUsage <= 2


====
