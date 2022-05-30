----------------------- MODULE DoubleBufferingV1Naive -----------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

Max(S) == CHOOSE i \in S : \A j \in S : i >= j
Abs(x) == Max({x, -x})

\* Number of iterations for the RT loop to run.
\* When the RT loop terminates, it also terminates the non-RT loop.
\* Action constraints in TLC should prevent the non-RT loop from infinitely
\* spinning.
CONSTANT RTIterations

(* --algorithm DoubleBufferingV1Naive
variables
  DoubleBuffer = <<0, 0>>,
  NonRTDataSeen = {},
  Index = 0, \* Index is zero or 1 to make it easier to negate, but needs to be 1-index for array access
  Stopped = FALSE;

fair process NonRTThread = "NonRTThread"
variables
  nonRTLocalBufIdx;
  nonRTDataRead;
  nonRTLoopIdx = 0; \* Used for action constraints more than anything else
begin
  non_rt_loop:
    while (Stopped # TRUE) do
      nonRTLoopIdx := nonRTLoopIdx + 1;

      non_rt_xor_idx:
        nonRTLocalBufIdx := Index || Index := Abs(Index - 1);

      non_rt_proc:
        nonRTDataRead := DoubleBuffer[nonRTLocalBufIdx + 1];
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
        DoubleBuffer[rtLocalBufIdx + 1] := rtData;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "23f010b5" /\ chksum(tla) = "26422565")
CONSTANT defaultInitValue
VARIABLES DoubleBuffer, NonRTDataSeen, Index, Stopped, pc, nonRTLocalBufIdx, 
          nonRTDataRead, nonRTLoopIdx, rtData, rtLocalBufIdx

vars == << DoubleBuffer, NonRTDataSeen, Index, Stopped, pc, nonRTLocalBufIdx, 
           nonRTDataRead, nonRTLoopIdx, rtData, rtLocalBufIdx >>

ProcSet == {"NonRTThread"} \cup {"RTThread"}

Init == (* Global variables *)
        /\ DoubleBuffer = <<0, 0>>
        /\ NonRTDataSeen = {}
        /\ Index = 0
        /\ Stopped = FALSE
        (* Process NonRTThread *)
        /\ nonRTLocalBufIdx = defaultInitValue
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
                          /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_xor_idx"]
                     ELSE /\ pc' = [pc EXCEPT !["NonRTThread"] = "Done"]
                          /\ UNCHANGED nonRTLoopIdx
               /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, Stopped, 
                               nonRTLocalBufIdx, nonRTDataRead, rtData, 
                               rtLocalBufIdx >>

non_rt_xor_idx == /\ pc["NonRTThread"] = "non_rt_xor_idx"
                  /\ /\ Index' = Abs(Index - 1)
                     /\ nonRTLocalBufIdx' = Index
                  /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_proc"]
                  /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Stopped, 
                                  nonRTDataRead, nonRTLoopIdx, rtData, 
                                  rtLocalBufIdx >>

non_rt_proc == /\ pc["NonRTThread"] = "non_rt_proc"
               /\ nonRTDataRead' = DoubleBuffer[nonRTLocalBufIdx + 1]
               /\ Assert(Cardinality({data \in NonRTDataSeen : data > nonRTDataRead'}) = 0, 
                         "Failure of assertion at line 44, column 9.")
               /\ NonRTDataSeen' = (NonRTDataSeen \union {nonRTDataRead'})
               /\ pc' = [pc EXCEPT !["NonRTThread"] = "non_rt_loop"]
               /\ UNCHANGED << DoubleBuffer, Index, Stopped, nonRTLocalBufIdx, 
                               nonRTLoopIdx, rtData, rtLocalBufIdx >>

NonRTThread == non_rt_loop \/ non_rt_xor_idx \/ non_rt_proc

rt_generate_data == /\ pc["RTThread"] = "rt_generate_data"
                    /\ IF (rtData < RTIterations)
                          THEN /\ rtData' = rtData + 1
                               /\ pc' = [pc EXCEPT !["RTThread"] = "rt_read_idx"]
                          ELSE /\ pc' = [pc EXCEPT !["RTThread"] = "Done"]
                               /\ UNCHANGED rtData
                    /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, 
                                    Stopped, nonRTLocalBufIdx, nonRTDataRead, 
                                    nonRTLoopIdx, rtLocalBufIdx >>

rt_read_idx == /\ pc["RTThread"] = "rt_read_idx"
               /\ rtLocalBufIdx' = Index
               /\ pc' = [pc EXCEPT !["RTThread"] = "rt_write_buf"]
               /\ UNCHANGED << DoubleBuffer, NonRTDataSeen, Index, Stopped, 
                               nonRTLocalBufIdx, nonRTDataRead, nonRTLoopIdx, 
                               rtData >>

rt_write_buf == /\ pc["RTThread"] = "rt_write_buf"
                /\ DoubleBuffer' = [DoubleBuffer EXCEPT ![rtLocalBufIdx + 1] = rtData]
                /\ pc' = [pc EXCEPT !["RTThread"] = "rt_generate_data"]
                /\ UNCHANGED << NonRTDataSeen, Index, Stopped, 
                                nonRTLocalBufIdx, nonRTDataRead, nonRTLoopIdx, 
                                rtData, rtLocalBufIdx >>

RTThread == rt_generate_data \/ rt_read_idx \/ rt_write_buf

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

\* Invariants and temporal properties
\* ==================================
\* 
\* - Invariants
\* - Temporal properties
\*   - The data read by the non-RT thread should be monotonically increasing.
\*     - Implemented as a hacky assertion in an invariant like format. This has
\*       drawbacks when it comes to visualizing the invariant.
\*   - The data should be read by the non-RT thread at least once for some of
\*     the test cases.

=============================================================================
\* Modification History
\* Last modified Wed May 11 17:47:14 EDT 2022 by shuhao
\* Created Wed May 11 16:32:55 EDT 2022 by shuhao
