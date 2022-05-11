----------------------- MODULE DoubleBufferingV2NewData -----------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

Max(S) == CHOOSE i \in S : \A j \in S : i >= j
Abs(x) == Max({x, -x})

InverseIndex(index) == IF index = 1 THEN 2 ELSE 1

\* Number of iterations for the RT loop to run.
\* When the RT loop terminates, it also terminates the non-RT loop.
\* Action constraints in TLC should prevent the non-RT loop from infinitely
\* spinning.
CONSTANT RTIterations

(* --algorithm DoubleBufferingV1Naive
variables
  DoubleBuffer = <<0, 0>>,
  NonRTDataSeen = {},
  Index = 1, 
  NewData = FALSE, \* Not a bitwise implementation, but OK because TLA+ can do multiple assignments atomically.
  Stopped = FALSE;

fair process NonRTThread = "NonRTThread"
variables
  nonRTLocalBufIdx,
  nonRTLocalNewData,
  nonRTDataRead,
  nonRTLoopIdx = 0; \* Used for action constraints more than anything else
begin
  non_rt_loop:
    while (Stopped # TRUE) do
      nonRTLoopIdx := nonRTLoopIdx + 1;

      non_rt_idx_load:
        nonRTLocalBufIdx := Index;
        nonRTLocalNewData := NewData;
      
      non_rt_new_data_check:
        if (nonRTLocalNewData = TRUE) then
          non_rt_idx_inverse:
            nonRTLocalBufIdx := InverseIndex(nonRTLocalBufIdx);

          non_rt_idx_store:
            Index := nonRTLocalBufIdx;
            NewData := FALSE;
        end if;

      non_rt_proc:
        \* The Index always points to where the RT thread should write to
        nonRTDataRead := DoubleBuffer[InverseIndex(nonRTLocalBufIdx)];
        \* TODO: also implement this via a temporal condition, as nonRTDataRead
        \* should be monotonically increasing.
        \* It seems like the TLA+ trace for this error case doesn't include the 
        \* last state, or this state. It only appears to show the state prior to
        \* this one, presumably because this assertion stopped the execution.
        \* This is another reason why the temporal condition would be better.
        \* 
        \* Do not want >= because >= will not allow the same data to be seen.
        \* It is OK to see the same data multiple times if the RT thread hasn't updated.
        assert Cardinality({data \in NonRTDataSeen : data > nonRTDataRead}) = 0;
        NonRTDataSeen := NonRTDataSeen \union {nonRTDataRead};
        assert (pc["RTThread"] # "rt_write_buf" \/ rtLocalBufIdx # InverseIndex(nonRTLocalBufIdx));
    end while;
end process;

fair process RTThread = "RTThread"
variables
  rtData = 0,
  rtLocalBufIdx;
begin
  rt_generate_data:
    while (rtData < RTIterations) do \* Use the rtData to cheat a bit to terminate this algorithm
      rtData := rtData + 1;

      rt_read_idx:
        rtLocalBufIdx := Index;

      rt_write_buf:
        DoubleBuffer[rtLocalBufIdx] := rtData;
        assert (pc["NonRTThread"] # "non_rt_proc" \/ rtLocalBufIdx # InverseIndex(nonRTLocalBufIdx));

      rt_update_idx:
        Index := rtLocalBufIdx;
        NewData := TRUE;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "305793e9" /\ chksum(tla) = "f39853c9")
CONSTANT defaultInitValue
VARIABLES DoubleBuffer, NonRTDataSeen, Index, NewData, Stopped, pc, 
          nonRTLocalBufIdx, nonRTLocalNewData, nonRTDataRead, nonRTLoopIdx, 
          rtData, rtLocalBufIdx

vars == << DoubleBuffer, NonRTDataSeen, Index, NewData, Stopped, pc, 
           nonRTLocalBufIdx, nonRTLocalNewData, nonRTDataRead, nonRTLoopIdx, 
           rtData, rtLocalBufIdx >>

ProcSet == {"NonRTThread"} \cup {"RTThread"}

Init == (* Global variables *)
        /\ DoubleBuffer = <<0, 0>>
        /\ NonRTDataSeen = {}
        /\ Index = 1
        /\ NewData = FALSE
        /\ Stopped = FALSE
        (* Process NonRTThread *)
        /\ nonRTLocalBufIdx = defaultInitValue
        /\ nonRTLocalNewData = defaultInitValue
        /\ nonRTDataRead = defaultInitValue
        /\ nonRTLoopIdx = 0
        (* Process RTThread *)
        /\ rtData = 0
        /\ rtLocalBufIdx = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "NonRTThread" -> "non_rt_loop"
                                        [] self = "RTThread" -> "rt_generate_data"]

non_rt_loop == /\ pc["NonRTThread"] = "non_rt_loop"
               /\ IF (Stopped # TRUE)
                     THEN /\ nonRTLoopIdx' = nonRTLoopIdx + 1
                          /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_idx_load"]
                     ELSE /\ pc' = [pc EXCEPT !["NonRTThread"] = "Done"]
                          /\ UNCHANGED nonRTLoopIdx
               /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, NewData, 
                               Stopped, nonRTLocalBufIdx, nonRTLocalNewData, 
                               nonRTDataRead, rtData, rtLocalBufIdx >>

non_rt_idx_load == /\ pc["NonRTThread"] = "non_rt_idx_load"
                   /\ nonRTLocalBufIdx' = Index
                   /\ nonRTLocalNewData' = NewData
                   /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_new_data_check"]
                   /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, NewData, 
                                   Stopped, nonRTDataRead, nonRTLoopIdx, 
                                   rtData, rtLocalBufIdx >>

non_rt_new_data_check == /\ pc["NonRTThread"] = "non_rt_new_data_check"
                         /\ IF (nonRTLocalNewData = TRUE)
                               THEN /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_idx_inverse"]
                               ELSE /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_proc"]
                         /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, 
                                         NewData, Stopped, nonRTLocalBufIdx, 
                                         nonRTLocalNewData, nonRTDataRead, 
                                         nonRTLoopIdx, rtData, rtLocalBufIdx >>

non_rt_idx_inverse == /\ pc["NonRTThread"] = "non_rt_idx_inverse"
                      /\ nonRTLocalBufIdx' = InverseIndex(nonRTLocalBufIdx)
                      /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_idx_store"]
                      /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, 
                                      NewData, Stopped, nonRTLocalNewData, 
                                      nonRTDataRead, nonRTLoopIdx, rtData, 
                                      rtLocalBufIdx >>

non_rt_idx_store == /\ pc["NonRTThread"] = "non_rt_idx_store"
                    /\ Index' = nonRTLocalBufIdx
                    /\ NewData' = FALSE
                    /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_proc"]
                    /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Stopped, 
                                    nonRTLocalBufIdx, nonRTLocalNewData, 
                                    nonRTDataRead, nonRTLoopIdx, rtData, 
                                    rtLocalBufIdx >>

non_rt_proc == /\ pc["NonRTThread"] = "non_rt_proc"
               /\ nonRTDataRead' = DoubleBuffer[InverseIndex(nonRTLocalBufIdx)]
               /\ Assert(Cardinality({data \in NonRTDataSeen : data > nonRTDataRead'}) = 0, 
                         "Failure of assertion at line 60, column 9.")
               /\ NonRTDataSeen' = (NonRTDataSeen \union {nonRTDataRead'})
               /\ Assert((pc["RTThread"] # "rt_write_buf" \/ rtLocalBufIdx # InverseIndex(nonRTLocalBufIdx)), 
                         "Failure of assertion at line 62, column 9.")
               /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_loop"]
               /\ UNCHANGED << DoubleBuffer, Index, NewData, Stopped, 
                               nonRTLocalBufIdx, nonRTLocalNewData, 
                               nonRTLoopIdx, rtData, rtLocalBufIdx >>

NonRTThread == non_rt_loop \/ non_rt_idx_load \/ non_rt_new_data_check
                  \/ non_rt_idx_inverse \/ non_rt_idx_store \/ non_rt_proc

rt_generate_data == /\ pc["RTThread"] = "rt_generate_data"
                    /\ IF (rtData < RTIterations)
                          THEN /\ rtData' = rtData + 1
                               /\ pc' = [pc EXCEPT !["RTThread"] = "rt_read_idx"]
                          ELSE /\ pc' = [pc EXCEPT !["RTThread"] = "Done"]
                               /\ UNCHANGED rtData
                    /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, 
                                    NewData, Stopped, nonRTLocalBufIdx, 
                                    nonRTLocalNewData, nonRTDataRead, 
                                    nonRTLoopIdx, rtLocalBufIdx >>

rt_read_idx == /\ pc["RTThread"] = "rt_read_idx"
               /\ rtLocalBufIdx' = Index
               /\ pc' = [pc EXCEPT !["RTThread"] = "rt_write_buf"]
               /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, NewData, 
                               Stopped, nonRTLocalBufIdx, nonRTLocalNewData, 
                               nonRTDataRead, nonRTLoopIdx, rtData >>

rt_write_buf == /\ pc["RTThread"] = "rt_write_buf"
                /\ DoubleBuffer' = [DoubleBuffer EXCEPT ![rtLocalBufIdx] = rtData]
                /\ Assert((pc["NonRTThread"] # "non_rt_proc" \/ rtLocalBufIdx # InverseIndex(nonRTLocalBufIdx)), 
                          "Failure of assertion at line 80, column 9.")
                /\ pc' = [pc EXCEPT !["RTThread"] = "rt_update_idx"]
                /\ UNCHANGED << NonRTDataSeen, Index, NewData, Stopped, 
                                nonRTLocalBufIdx, nonRTLocalNewData, 
                                nonRTDataRead, nonRTLoopIdx, rtData, 
                                rtLocalBufIdx >>

rt_update_idx == /\ pc["RTThread"] = "rt_update_idx"
                 /\ Index' = rtLocalBufIdx
                 /\ NewData' = TRUE
                 /\ pc' = [pc EXCEPT !["RTThread"] = "rt_generate_data"]
                 /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Stopped, 
                                 nonRTLocalBufIdx, nonRTLocalNewData, 
                                 nonRTDataRead, nonRTLoopIdx, rtData, 
                                 rtLocalBufIdx >>

RTThread == rt_generate_data \/ rt_read_idx \/ rt_write_buf
               \/ rt_update_idx

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

ActionConstraintNonRTThreadDoesNotInfinitelySpin ==
  (nonRTLoopIdx - rtData) < 4

\* InvariantNoDataRace == 

\* Invariants and temporal properties
\* ==================================
\* 
\* - Invariants
\*   - The same slot in the double buffer cannot be written or read from at the 
\*     same time from the two threads.
\* - Temporal properties
\*   - The data read by the non-RT thread should be monotonically increasing.
\*     - Implemented as a hacky assertion in an invariant like format. This has
\*       drawbacks when it comes to visualizing the invariant.
\*   - The data should be read by the non-RT thread at least once for some of
\*     the test cases.

=============================================================================
\* Modification History
\* Last modified Thu May 12 00:22:54 EDT 2022 by shuhao
\* Created Wed May 11 16:32:55 EDT 2022 by shuhao
