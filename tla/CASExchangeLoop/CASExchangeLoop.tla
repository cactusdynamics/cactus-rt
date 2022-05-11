---- MODULE CASExchangeLoop ----
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

  OwnedPointer = 1,
  AtomicPointer = 1,

  \* Set to TRUE once the non-RT loop exits.
  Stopped = FALSE;

macro CompareAndSwap(oldValue, newValue, value, swapped) begin
  if (value = oldValue) then
    value := newValue;
    swapped := TRUE;
  else
    swapped := FALSE;
  end if;
end macro;

fair process NonRTThread = "NonRTThread"
  variables
    nonRTLocalDataPointer,
    expected,
    swapped = FALSE,
    nonRTLoopIdx = 0; \* Needed for the action constraint
begin
  non_rt_loop:
    while (Stopped # TRUE) do
      nonRTLoopIdx := nonRTLoopIdx + 1;
      swapped := FALSE;
      non_rt_new:
        nonRTLocalDataPointer := CHOOSE i \in DOMAIN Memory : Memory[i] = Uninitialized;
        Memory[nonRTLocalDataPointer] := nonRTLocalDataPointer;
        \* This checks that there's no data race with the rt_proc.
        \* It is kind of a hack, but I'm not 100% certain how to write an invariant for this.
        assert (pc["RTThread"] # "rt_proc" \/ nonRTLocalDataPointer # rtLocalDataPointer);
      non_rt_cas_loop:
        while (swapped = FALSE) do
          non_rt_cas_step1:
            expected := OwnedPointer;
          non_rt_cas_step2:
            CompareAndSwap(expected, nonRTLocalDataPointer, AtomicPointer, swapped);
        end while;
      non_rt_delete_data:
        Memory[OwnedPointer] := Uninitialized;
        \* This checks that there's no data race with the rt_proc.
        \* It is kind of a hack, but I'm not 100% certain how to write an invariant for this.
        assert (pc["RTThread"] # "rt_proc" \/ OwnedPointer # rtLocalDataPointer);
      non_rt_move_pointer:
        OwnedPointer := nonRTLocalDataPointer;
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
      rt_exchange:
        \* Exchange the global pointer with "null" pointer in an atomic step.
        rtLocalDataPointer := AtomicPointer || AtomicPointer := 0;
      rt_proc:
        skip;
        \* The following should be caught by the invariant, so it is skipped for now.
        \* assert Memory[rtLocalDataPointer] # Uninitialized;
      rt_set_back:
        AtomicPointer := rtLocalDataPointer;
    end while;
    Stopped := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "972fce36" /\ chksum(tla) = "66515f9d")
CONSTANT defaultInitValue
VARIABLES Memory, OwnedPointer, AtomicPointer, Stopped, pc,
          nonRTLocalDataPointer, expected, swapped, nonRTLoopIdx,
          rtLocalDataPointer, rtLoopIdx

vars == << Memory, OwnedPointer, AtomicPointer, Stopped, pc,
           nonRTLocalDataPointer, expected, swapped, nonRTLoopIdx,
           rtLocalDataPointer, rtLoopIdx >>

ProcSet == {"NonRTThread"} \cup {"RTThread"}

Init == (* Global variables *)
        /\ Memory = [i \in 1..MemoryCapacity |-> IF i = 1 THEN 1 ELSE Uninitialized]
        /\ OwnedPointer = 1
        /\ AtomicPointer = 1
        /\ Stopped = FALSE
        (* Process NonRTThread *)
        /\ nonRTLocalDataPointer = defaultInitValue
        /\ expected = defaultInitValue
        /\ swapped = FALSE
        /\ nonRTLoopIdx = 0
        (* Process RTThread *)
        /\ rtLocalDataPointer = defaultInitValue
        /\ rtLoopIdx = 0
        /\ pc = [self \in ProcSet |-> CASE self = "NonRTThread" -> "non_rt_loop"
                                        [] self = "RTThread" -> "rt_loop"]

non_rt_loop == /\ pc["NonRTThread"] = "non_rt_loop"
               /\ IF (Stopped # TRUE)
                     THEN /\ nonRTLoopIdx' = nonRTLoopIdx + 1
                          /\ swapped' = FALSE
                          /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_new"]
                     ELSE /\ pc' = [pc EXCEPT !["NonRTThread"] = "Done"]
                          /\ UNCHANGED << swapped, nonRTLoopIdx >>
               /\ UNCHANGED << Memory, OwnedPointer, AtomicPointer, Stopped,
                               nonRTLocalDataPointer, expected,
                               rtLocalDataPointer, rtLoopIdx >>

non_rt_new == /\ pc["NonRTThread"] = "non_rt_new"
              /\ nonRTLocalDataPointer' = (CHOOSE i \in DOMAIN Memory : Memory[i] = Uninitialized)
              /\ Memory' = [Memory EXCEPT ![nonRTLocalDataPointer'] = nonRTLocalDataPointer']
              /\ Assert((pc["RTThread"] # "rt_proc" \/ nonRTLocalDataPointer' # rtLocalDataPointer),
                        "Failure of assertion at line 52, column 9.")
              /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_cas_loop"]
              /\ UNCHANGED << OwnedPointer, AtomicPointer, Stopped, expected,
                              swapped, nonRTLoopIdx, rtLocalDataPointer,
                              rtLoopIdx >>

non_rt_cas_loop == /\ pc["NonRTThread"] = "non_rt_cas_loop"
                   /\ IF (swapped = FALSE)
                         THEN /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_cas_step1"]
                         ELSE /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_delete_data"]
                   /\ UNCHANGED << Memory, OwnedPointer, AtomicPointer,
                                   Stopped, nonRTLocalDataPointer, expected,
                                   swapped, nonRTLoopIdx, rtLocalDataPointer,
                                   rtLoopIdx >>

non_rt_cas_step1 == /\ pc["NonRTThread"] = "non_rt_cas_step1"
                    /\ expected' = OwnedPointer
                    /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_cas_step2"]
                    /\ UNCHANGED << Memory, OwnedPointer, AtomicPointer,
                                    Stopped, nonRTLocalDataPointer, swapped,
                                    nonRTLoopIdx, rtLocalDataPointer,
                                    rtLoopIdx >>

non_rt_cas_step2 == /\ pc["NonRTThread"] = "non_rt_cas_step2"
                    /\ IF (AtomicPointer = expected)
                          THEN /\ AtomicPointer' = nonRTLocalDataPointer
                               /\ swapped' = TRUE
                          ELSE /\ swapped' = FALSE
                               /\ UNCHANGED AtomicPointer
                    /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_cas_loop"]
                    /\ UNCHANGED << Memory, OwnedPointer, Stopped,
                                    nonRTLocalDataPointer, expected,
                                    nonRTLoopIdx, rtLocalDataPointer,
                                    rtLoopIdx >>

non_rt_delete_data == /\ pc["NonRTThread"] = "non_rt_delete_data"
                      /\ Memory' = [Memory EXCEPT ![OwnedPointer] = Uninitialized]
                      /\ Assert((pc["RTThread"] # "rt_proc" \/ OwnedPointer # rtLocalDataPointer),
                                "Failure of assertion at line 64, column 9.")
                      /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_move_pointer"]
                      /\ UNCHANGED << OwnedPointer, AtomicPointer, Stopped,
                                      nonRTLocalDataPointer, expected, swapped,
                                      nonRTLoopIdx, rtLocalDataPointer,
                                      rtLoopIdx >>

non_rt_move_pointer == /\ pc["NonRTThread"] = "non_rt_move_pointer"
                       /\ OwnedPointer' = nonRTLocalDataPointer
                       /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_loop"]
                       /\ UNCHANGED << Memory, AtomicPointer, Stopped,
                                       nonRTLocalDataPointer, expected,
                                       swapped, nonRTLoopIdx,
                                       rtLocalDataPointer, rtLoopIdx >>

NonRTThread == non_rt_loop \/ non_rt_new \/ non_rt_cas_loop
                  \/ non_rt_cas_step1 \/ non_rt_cas_step2
                  \/ non_rt_delete_data \/ non_rt_move_pointer

rt_loop == /\ pc["RTThread"] = "rt_loop"
           /\ IF (rtLoopIdx < RTIterations)
                 THEN /\ rtLoopIdx' = rtLoopIdx + 1
                      /\ pc' = [pc EXCEPT !["RTThread"] = "rt_exchange"]
                      /\ UNCHANGED Stopped
                 ELSE /\ Stopped' = TRUE
                      /\ pc' = [pc EXCEPT !["RTThread"] = "Done"]
                      /\ UNCHANGED rtLoopIdx
           /\ UNCHANGED << Memory, OwnedPointer, AtomicPointer,
                           nonRTLocalDataPointer, expected, swapped,
                           nonRTLoopIdx, rtLocalDataPointer >>

rt_exchange == /\ pc["RTThread"] = "rt_exchange"
               /\ /\ AtomicPointer' = 0
                  /\ rtLocalDataPointer' = AtomicPointer
               /\ pc' = [pc EXCEPT !["RTThread"] = "rt_proc"]
               /\ UNCHANGED << Memory, OwnedPointer, Stopped,
                               nonRTLocalDataPointer, expected, swapped,
                               nonRTLoopIdx, rtLoopIdx >>

rt_proc == /\ pc["RTThread"] = "rt_proc"
           /\ TRUE
           /\ pc' = [pc EXCEPT !["RTThread"] = "rt_set_back"]
           /\ UNCHANGED << Memory, OwnedPointer, AtomicPointer, Stopped,
                           nonRTLocalDataPointer, expected, swapped,
                           nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx >>

rt_set_back == /\ pc["RTThread"] = "rt_set_back"
               /\ AtomicPointer' = rtLocalDataPointer
               /\ pc' = [pc EXCEPT !["RTThread"] = "rt_loop"]
               /\ UNCHANGED << Memory, OwnedPointer, Stopped,
                               nonRTLocalDataPointer, expected, swapped,
                               nonRTLoopIdx, rtLocalDataPointer, rtLoopIdx >>

RTThread == rt_loop \/ rt_exchange \/ rt_proc \/ rt_set_back

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

\* Invariants and temporal properties to check
\* ===========================================
\* - Invariants
\*   - Ensure there are no access to uninitialized memory
\*   - Ensure there are no memory leaks (memory usage remains bounded)
\*   - Ensure there are no data races: when the RT thread has access to the
\*     variable, make sure the non-RT thread cannot write to it.
\*     - This is implemented as an assertion inline and seems a bit hacky. An o
\*       invariant or temporal property would serve this much better.
\* - Temporal properties
\*   - Ensure that the RT thread actually reads the data in "some cases".
\*     - This is not well-defined enough to write as a property.
\*   - Ensure that the RT thread eventually reads the "latest" data and not a past data.
\*     - Also badly defined so it cannot be written as a property for now.

\* Makes sure the RT thread never accesses uninitialized memory.
InvariantNoUninitializedMemoryAccess ==
  (pc["RTThread"] = "rt_proc") => (Memory[rtLocalDataPointer] # Uninitialized)

\* Makes sure we don't use an infinite amount of memory
InvariantNoMemoryLeak ==
  MemoryUsage <= 2

\* TODO: need a temporary property to ensure that the RT loop eventually read the data?


====
