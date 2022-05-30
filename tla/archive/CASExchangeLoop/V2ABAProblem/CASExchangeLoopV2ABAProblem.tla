---- MODULE CASExchangeLoopV2ABAProblem ----
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

  \* A atomic flag for whether or not the RT thread is active and using the pointer.
  \* Spoiler: this approach doesn't work either.
  InRTThread = FALSE,

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
      non_rt_wait_for_flag:
        while (InRTThread) do
          skip;
        end while;
      non_rt_swap:
        \* A swap operation
        DataPointer := nonRTLocalDataPointer || nonRTLocalDataPointer := DataPointer;
      non_rt_delete:
        Memory[nonRTLocalDataPointer] := Uninitialized;
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
      rt_set_flag:
        InRTThread := TRUE;
      rt_load:
        rtLocalDataPointer := DataPointer;
      rt_proc:
        skip; 
        \* Should be caught by the invariant.
        \* assert Memory[rtLocalDataPointer] # Uninitialized;
      rt_unset_flag:
        InRTThread := FALSE;
    end while;
    Stopped := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9836b2bf" /\ chksum(tla) = "3abe601a")
CONSTANT defaultInitValue
VARIABLES Memory, DataPointer, InRTThread, Stopped, pc, nonRTLocalDataPointer, 
          nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx

vars == << Memory, DataPointer, InRTThread, Stopped, pc, 
           nonRTLocalDataPointer, nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx
        >>

ProcSet == {"NonRTThread"} \cup {"RTThread"}

Init == (* Global variables *)
        /\ Memory = [i \in 1..MemoryCapacity |-> IF i = 1 THEN 1 ELSE Uninitialized]
        /\ DataPointer = 1
        /\ InRTThread = FALSE
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
               /\ UNCHANGED << Memory, DataPointer, InRTThread, Stopped, 
                               nonRTLocalDataPointer, rtLocalDataPointer, 
                               rtLoopIdx >>

non_rt_new == /\ pc["NonRTThread"] = "non_rt_new"
              /\ nonRTLocalDataPointer' = (CHOOSE i \in DOMAIN Memory : Memory[i] = Uninitialized)
              /\ Memory' = [Memory EXCEPT ![nonRTLocalDataPointer'] = nonRTLocalDataPointer']
              /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_wait_for_flag"]
              /\ UNCHANGED << DataPointer, InRTThread, Stopped, nonRTLoopIdx, 
                              rtLocalDataPointer, rtLoopIdx >>

non_rt_wait_for_flag == /\ pc["NonRTThread"] = "non_rt_wait_for_flag"
                        /\ IF (InRTThread)
                              THEN /\ TRUE
                                   /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_wait_for_flag"]
                              ELSE /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_swap"]
                        /\ UNCHANGED << Memory, DataPointer, InRTThread, 
                                        Stopped, nonRTLocalDataPointer, 
                                        nonRTLoopIdx, rtLocalDataPointer, 
                                        rtLoopIdx >>

non_rt_swap == /\ pc["NonRTThread"] = "non_rt_swap"
               /\ /\ DataPointer' = nonRTLocalDataPointer
                  /\ nonRTLocalDataPointer' = DataPointer
               /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_delete"]
               /\ UNCHANGED << Memory, InRTThread, Stopped, nonRTLoopIdx, 
                               rtLocalDataPointer, rtLoopIdx >>

non_rt_delete == /\ pc["NonRTThread"] = "non_rt_delete"
                 /\ Memory' = [Memory EXCEPT ![nonRTLocalDataPointer] = Uninitialized]
                 /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_loop"]
                 /\ UNCHANGED << DataPointer, InRTThread, Stopped, 
                                 nonRTLocalDataPointer, nonRTLoopIdx, 
                                 rtLocalDataPointer, rtLoopIdx >>

NonRTThread == non_rt_loop \/ non_rt_new \/ non_rt_wait_for_flag
                  \/ non_rt_swap \/ non_rt_delete

rt_loop == /\ pc["RTThread"] = "rt_loop"
           /\ IF (rtLoopIdx < RTIterations)
                 THEN /\ rtLoopIdx' = rtLoopIdx + 1
                      /\ pc' = [pc EXCEPT !["RTThread"] = "rt_set_flag"]
                      /\ UNCHANGED Stopped
                 ELSE /\ Stopped' = TRUE
                      /\ pc' = [pc EXCEPT !["RTThread"] = "Done"]
                      /\ UNCHANGED rtLoopIdx
           /\ UNCHANGED << Memory, DataPointer, InRTThread, 
                           nonRTLocalDataPointer, nonRTLoopIdx, 
                           rtLocalDataPointer >>

rt_set_flag == /\ pc["RTThread"] = "rt_set_flag"
               /\ InRTThread' = TRUE
               /\ pc' = [pc EXCEPT !["RTThread"] = "rt_load"]
               /\ UNCHANGED << Memory, DataPointer, Stopped, 
                               nonRTLocalDataPointer, nonRTLoopIdx, 
                               rtLocalDataPointer, rtLoopIdx >>

rt_load == /\ pc["RTThread"] = "rt_load"
           /\ rtLocalDataPointer' = DataPointer
           /\ pc' = [pc EXCEPT !["RTThread"] = "rt_proc"]
           /\ UNCHANGED << Memory, DataPointer, InRTThread, Stopped, 
                           nonRTLocalDataPointer, nonRTLoopIdx, rtLoopIdx >>

rt_proc == /\ pc["RTThread"] = "rt_proc"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["RTThread"] = "rt_unset_flag"]
           /\ UNCHANGED << Memory, DataPointer, InRTThread, Stopped, 
                           nonRTLocalDataPointer, nonRTLoopIdx, 
                           rtLocalDataPointer, rtLoopIdx >>

rt_unset_flag == /\ pc["RTThread"] = "rt_unset_flag"
                 /\ InRTThread' = FALSE
                 /\ pc' = [pc EXCEPT !["RTThread"] = "rt_loop"]
                 /\ UNCHANGED << Memory, DataPointer, Stopped, 
                                 nonRTLocalDataPointer, nonRTLoopIdx, 
                                 rtLocalDataPointer, rtLoopIdx >>

RTThread == rt_loop \/ rt_set_flag \/ rt_load \/ rt_proc \/ rt_unset_flag

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
