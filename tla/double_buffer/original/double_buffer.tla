---- MODULE double_buffer ----
EXTENDS Sequences, Integers, TLC, FiniteSets

(******************************************************************************
 This implements the double buffer algorithm original introduced by by Dave
 Rowland and Fabien Renn-Giles in Real-time 101 - Part II: The real-time audio
 developer's toolbox (https://youtu.be/PoZAo2Vikbo?t=722).

 This model contains two processes: a reader and a writer. Both of these
 processes operates with a loop, which implies that reading and writing occurs
 multiple times. While in the real-world the reader and writer can continue
 indefinitely, the model has both of these processes quite after
 kTotalIterationsCount, to bound the search space.

 The reader and writer exchange data via g_slots. The data written is a sequence
 of the same integer values that are monotonically increasing. The reader and
 writer can only read or write one value atomically, allowing us to detect data
 races via torn writes. Since the writer is supposed to write the same integer
 value to the sequence, a torn write can be easily detected if the cardinality
 of the set of sequence values is greater than 1. As a concrete example:

 1. Initially, the data in the slot is <<0, 0>>.
 2. The writer starts writing to the slot, changing the first value: <<1, 0>>.
    If the reader starts reading the same slot, there's a data race and we can
    detect this as the value in the slot is torn.
 3. The writer continues writing to the slot, changing the second value:
    <<1, 1>>. At this point, the data is no longer torn.
 4. In the next iteration, the writer would try to write <<2, 2>>.
 5. In the iteration after that, the writer would try to writer <<3, 3>>

 Since the writer is monotonically increasing the value written, it is also
 relatively easier for the reader to detect that an older value has been
 written. The reader shouldn't be able to read an older, invalid value. If the
 algorithm is improperly coded, this can occur, as mentioned in the original
 presentation, if the reader reads twice before the writer writes.

 In the original presentation, bits are used to indicate the active slot, the
 availability of new data, and the busy-ness of the writer. For simplicity, this
 model uses a record and atomically updates it, which emulates the same
 standard.

 The model uses a number of state variables that are not actually a part of the
 algorithm for modeling and assertion reasons. These variables are prefixed with
 h and uses hCamelCase. State variables actually participating in the algorithm
 are in snake_case. Global variables are prefixed with g, reader-local variables
 are prefixed with r, and writer-local variables are prefixed with w.

 ******************************************************************************)

(*
 This is the total number of iterations that both the reader and writer should
 execute before the processes exit. While this can be infinite, it is finite
 (>=3) in the model to make TLC feasible.
 *)
CONSTANT kTotalIterationsCount

(*
 This is the size of the object. Each object has kObjectSize elements.

 For modeling purposes, we should set this to be greater than 1 to allow
 detection of data race (with torn reads/writes).
 *)
CONSTANT kObjectSize

(*
 A helper operator to create an object.
 *)
ObjectWithValue(value) == [i \in 1..kObjectSize |-> value]

(*
 A helper operator to flip the index so the code is not repeated.
 *)
FlipIndex(index) == IF index = 1 THEN 2 ELSE 1

(*
 A helper operator to check if a particular data is torn or not.
 *)
DataIsNotTorn(data) == Cardinality({data[i] : i \in 1..kObjectSize}) = 1

(*--algorithm double_buffer

variables
    kStartingIdx \in 1..2,
    g_slots = <<
        ObjectWithValue(0),
        ObjectWithValue(0)
    >>,
    g_idx = [idx |-> kStartingIdx, newdata |-> FALSE, busy |-> FALSE],
    hWriterMaximumData = 0;

fair process reader = "reader"
variables
    \* current in the original code
    r_current,
    \* newValue in the original code
    r_new_value,
    \* This keeps track of the current index that the reader is reading from
    \* the slots.
    \* Not present in the original as reading of the data is done implicitly.
    r_data_read_i,
    \* This is a local copy of the data that is read.
    \* Also not present in the original as this is done implicitly.
    r_local_data,
    \* Controls how many times the reader reads. This controls the size of
    \* the model checking state space.
    hReaderOuterLoopIdx = 1,
    \* Keeps track whether or not we have new data or not. This is used for
    \* assertion to ensure that when we get new data, we never read old data.
    hReaderGotNewData,
    \* Keeps track of the maximum data the reader have read so far.
    hReaderMaximumData = 0;
begin
    ReaderOuterLoop:
        while hReaderOuterLoopIdx <= kTotalIterationsCount do
            \* Reset all the local variables for the start of the new iteration.
            r_data_read_i := 1;
            r_local_data := ObjectWithValue(0);
            hReaderGotNewData := FALSE;
            hReaderOuterLoopIdx := hReaderOuterLoopIdx + 1;

            ReaderLoadIndex:
                r_current := g_idx;

            ReaderCheckNewData:
                if (r_current.newdata = TRUE) then
                    ReaderCASPrep:
                        \* current &= ~BIT_BUSY
                        \* This negates the busy bit
                        r_current := [
                            idx |-> r_current.idx,
                            newdata |-> r_current.newdata,
                            busy |-> FALSE
                        ];

                        \* newValue = (current ^ BIT_IDX) & BIT_IDX
                        \* This flips the idx bit then negates everything except the idx bit.
                        r_new_value := [
                            idx |-> FlipIndex(r_current.idx),
                            newdata |-> FALSE,
                            busy |-> FALSE
                        ];

                    ReaderCAS:
                        \* while (!idx.compare_exchange_weak(current, newValue))
                        if (g_idx # r_current) then
                            r_current := g_idx;
                            goto ReaderCASPrep;
                        else
                            g_idx := r_new_value;
                            \* current = newValue
                            r_current := r_new_value;
                            hReaderGotNewData := TRUE;
                        end if;
                end if;

            ReaderReadDataLoop:
                \* Note, r_current.idx is the idx of the writer, not the reader.
                \* Thus we need to flip the idx to read here.
                while r_data_read_i <= kObjectSize do
                    \* This ensures that when we are reading the data, we cannot
                    \* have a torn write/data race at the same time.
                    \* TODO: see if there is a better way to check for data race.
                    assert DataIsNotTorn(g_slots[FlipIndex(r_current.idx)]);

                    r_local_data[r_data_read_i] := g_slots[FlipIndex(r_current.idx)][r_data_read_i];
                    r_data_read_i := r_data_read_i + 1;
                end while;

            ReaderAfterReadData:
                \* This entire step is not in the original algorithm and only
                \* exists to check for correctness in TLC.

                \* Check to make sure that there's no torn read.
                assert DataIsNotTorn(r_local_data);

                \* Check to make sure that if we we got new data, the data read
                \* is always newer than what we have read before.
                \* TODO: this check has an issue where if the reader never got
                \* new data, then the second part of the OR statement never gets
                \* evaluated. This is not possible to fix within TLA+ as it is
                \* linear-time temporal logic and would require some sort of
                \* TLC-specific extensions.
                \*
                \* See https://groups.google.com/g/tlaplus/c/gVdl99UIkLU/m/aMkOQhieAQAJ
                assert
                    \/ ~hReaderGotNewData
                    \/ \A i \in 1..kObjectSize: r_local_data[i] > hReaderMaximumData;

                \* Record the new maximum data if we received new data so it can
                \* be used for assertions in the next iteration.
                if (hReaderGotNewData = TRUE) then
                    hReaderMaximumData := r_local_data[1];
                end if;
        end while;
end process;

fair process writer = "writer"
variables
    \* i in the original code, where the write index is read to by the writer.
    w_idx,
    \* This keeps track of the current position of the write.
    \* This is technically not a part of the original code, as the memcpy there
    \* is done implicitly, while we model it here explicitly.
    w_data_write_i,
    \* Controls how many times the writer writes. This controls the size of the
    \* state checking space
    hWriterOuterLoopIdx = 1;
begin
    WriterOuterLoop:
        while hWriterOuterLoopIdx <= kTotalIterationsCount do
            \* Reset variables to some initial state
            hWriterOuterLoopIdx := hWriterOuterLoopIdx + 1;
            w_data_write_i := 1;

            WriterLoadIdx:
                \* auto i = idx.fetch_or(BIT_BUSY) & BIT_IDX
                \* fetch_or updates idx with the idx | BIT_BUSY and returns idx prior to the update
                w_idx := g_idx.idx;
                g_idx.busy := TRUE;

            WriterWriteDataLoop:
                \* mostRecentSpectrum[i] = freqSpec;
                while w_data_write_i <= kObjectSize do
                    g_slots[w_idx][w_data_write_i] := hWriterMaximumData + 1;
                    w_data_write_i := w_data_write_i + 1;
                end while;

            WriterAfterWriteData:
                \* idx.store((i & BIT_IDX) | BIT_NEWDATA)
                g_idx.busy := FALSE || g_idx.newdata := TRUE;
                hWriterMaximumData := hWriterMaximumData + 1;
        end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b28165af" /\ chksum(tla) = "7c2f2fcf")
CONSTANT defaultInitValue
VARIABLES kStartingIdx, g_slots, g_idx, hWriterMaximumData, pc, r_current, 
          r_new_value, r_data_read_i, r_local_data, hReaderOuterLoopIdx, 
          hReaderGotNewData, hReaderMaximumData, w_idx, w_data_write_i, 
          hWriterOuterLoopIdx

vars == << kStartingIdx, g_slots, g_idx, hWriterMaximumData, pc, r_current, 
           r_new_value, r_data_read_i, r_local_data, hReaderOuterLoopIdx, 
           hReaderGotNewData, hReaderMaximumData, w_idx, w_data_write_i, 
           hWriterOuterLoopIdx >>

ProcSet == {"reader"} \cup {"writer"}

Init == (* Global variables *)
        /\ kStartingIdx \in 1..2
        /\ g_slots =           <<
                         ObjectWithValue(0),
                         ObjectWithValue(0)
                     >>
        /\ g_idx = [idx |-> kStartingIdx, newdata |-> FALSE, busy |-> FALSE]
        /\ hWriterMaximumData = 0
        (* Process reader *)
        /\ r_current = defaultInitValue
        /\ r_new_value = defaultInitValue
        /\ r_data_read_i = defaultInitValue
        /\ r_local_data = defaultInitValue
        /\ hReaderOuterLoopIdx = 1
        /\ hReaderGotNewData = defaultInitValue
        /\ hReaderMaximumData = 0
        (* Process writer *)
        /\ w_idx = defaultInitValue
        /\ w_data_write_i = defaultInitValue
        /\ hWriterOuterLoopIdx = 1
        /\ pc = [self \in ProcSet |-> CASE self = "reader" -> "ReaderOuterLoop"
                                        [] self = "writer" -> "WriterOuterLoop"]

ReaderOuterLoop == /\ pc["reader"] = "ReaderOuterLoop"
                   /\ IF hReaderOuterLoopIdx <= kTotalIterationsCount
                         THEN /\ r_data_read_i' = 1
                              /\ r_local_data' = ObjectWithValue(0)
                              /\ hReaderGotNewData' = FALSE
                              /\ hReaderOuterLoopIdx' = hReaderOuterLoopIdx + 1
                              /\ pc' = [pc EXCEPT !["reader"] = "ReaderLoadIndex"]
                         ELSE /\ pc' = [pc EXCEPT !["reader"] = "Done"]
                              /\ UNCHANGED << r_data_read_i, r_local_data, 
                                              hReaderOuterLoopIdx, 
                                              hReaderGotNewData >>
                   /\ UNCHANGED << kStartingIdx, g_slots, g_idx, 
                                   hWriterMaximumData, r_current, r_new_value, 
                                   hReaderMaximumData, w_idx, w_data_write_i, 
                                   hWriterOuterLoopIdx >>

ReaderLoadIndex == /\ pc["reader"] = "ReaderLoadIndex"
                   /\ r_current' = g_idx
                   /\ pc' = [pc EXCEPT !["reader"] = "ReaderCheckNewData"]
                   /\ UNCHANGED << kStartingIdx, g_slots, g_idx, 
                                   hWriterMaximumData, r_new_value, 
                                   r_data_read_i, r_local_data, 
                                   hReaderOuterLoopIdx, hReaderGotNewData, 
                                   hReaderMaximumData, w_idx, w_data_write_i, 
                                   hWriterOuterLoopIdx >>

ReaderCheckNewData == /\ pc["reader"] = "ReaderCheckNewData"
                      /\ IF (r_current.newdata = TRUE)
                            THEN /\ pc' = [pc EXCEPT !["reader"] = "ReaderCASPrep"]
                            ELSE /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadDataLoop"]
                      /\ UNCHANGED << kStartingIdx, g_slots, g_idx, 
                                      hWriterMaximumData, r_current, 
                                      r_new_value, r_data_read_i, r_local_data, 
                                      hReaderOuterLoopIdx, hReaderGotNewData, 
                                      hReaderMaximumData, w_idx, 
                                      w_data_write_i, hWriterOuterLoopIdx >>

ReaderCASPrep == /\ pc["reader"] = "ReaderCASPrep"
                 /\ r_current' =              [
                                     idx |-> r_current.idx,
                                     newdata |-> r_current.newdata,
                                     busy |-> FALSE
                                 ]
                 /\ r_new_value' =                [
                                       idx |-> FlipIndex(r_current'.idx),
                                       newdata |-> FALSE,
                                       busy |-> FALSE
                                   ]
                 /\ pc' = [pc EXCEPT !["reader"] = "ReaderCAS"]
                 /\ UNCHANGED << kStartingIdx, g_slots, g_idx, 
                                 hWriterMaximumData, r_data_read_i, 
                                 r_local_data, hReaderOuterLoopIdx, 
                                 hReaderGotNewData, hReaderMaximumData, w_idx, 
                                 w_data_write_i, hWriterOuterLoopIdx >>

ReaderCAS == /\ pc["reader"] = "ReaderCAS"
             /\ IF (g_idx # r_current)
                   THEN /\ r_current' = g_idx
                        /\ pc' = [pc EXCEPT !["reader"] = "ReaderCASPrep"]
                        /\ UNCHANGED << g_idx, hReaderGotNewData >>
                   ELSE /\ g_idx' = r_new_value
                        /\ r_current' = r_new_value
                        /\ hReaderGotNewData' = TRUE
                        /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadDataLoop"]
             /\ UNCHANGED << kStartingIdx, g_slots, hWriterMaximumData, 
                             r_new_value, r_data_read_i, r_local_data, 
                             hReaderOuterLoopIdx, hReaderMaximumData, w_idx, 
                             w_data_write_i, hWriterOuterLoopIdx >>

ReaderReadDataLoop == /\ pc["reader"] = "ReaderReadDataLoop"
                      /\ IF r_data_read_i <= kObjectSize
                            THEN /\ Assert(DataIsNotTorn(g_slots[FlipIndex(r_current.idx)]), 
                                           "Failure of assertion at line 163, column 21.")
                                 /\ r_local_data' = [r_local_data EXCEPT ![r_data_read_i] = g_slots[FlipIndex(r_current.idx)][r_data_read_i]]
                                 /\ r_data_read_i' = r_data_read_i + 1
                                 /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadDataLoop"]
                            ELSE /\ pc' = [pc EXCEPT !["reader"] = "ReaderAfterReadData"]
                                 /\ UNCHANGED << r_data_read_i, r_local_data >>
                      /\ UNCHANGED << kStartingIdx, g_slots, g_idx, 
                                      hWriterMaximumData, r_current, 
                                      r_new_value, hReaderOuterLoopIdx, 
                                      hReaderGotNewData, hReaderMaximumData, 
                                      w_idx, w_data_write_i, 
                                      hWriterOuterLoopIdx >>

ReaderAfterReadData == /\ pc["reader"] = "ReaderAfterReadData"
                       /\ Assert(DataIsNotTorn(r_local_data), 
                                 "Failure of assertion at line 174, column 17.")
                       /\ Assert(\/ ~hReaderGotNewData
                                 \/ \A i \in 1..kObjectSize: r_local_data[i] > hReaderMaximumData, 
                                 "Failure of assertion at line 185, column 17.")
                       /\ IF (hReaderGotNewData = TRUE)
                             THEN /\ hReaderMaximumData' = r_local_data[1]
                             ELSE /\ TRUE
                                  /\ UNCHANGED hReaderMaximumData
                       /\ pc' = [pc EXCEPT !["reader"] = "ReaderOuterLoop"]
                       /\ UNCHANGED << kStartingIdx, g_slots, g_idx, 
                                       hWriterMaximumData, r_current, 
                                       r_new_value, r_data_read_i, 
                                       r_local_data, hReaderOuterLoopIdx, 
                                       hReaderGotNewData, w_idx, 
                                       w_data_write_i, hWriterOuterLoopIdx >>

reader == ReaderOuterLoop \/ ReaderLoadIndex \/ ReaderCheckNewData
             \/ ReaderCASPrep \/ ReaderCAS \/ ReaderReadDataLoop
             \/ ReaderAfterReadData

WriterOuterLoop == /\ pc["writer"] = "WriterOuterLoop"
                   /\ IF hWriterOuterLoopIdx <= kTotalIterationsCount
                         THEN /\ hWriterOuterLoopIdx' = hWriterOuterLoopIdx + 1
                              /\ w_data_write_i' = 1
                              /\ pc' = [pc EXCEPT !["writer"] = "WriterLoadIdx"]
                         ELSE /\ pc' = [pc EXCEPT !["writer"] = "Done"]
                              /\ UNCHANGED << w_data_write_i, 
                                              hWriterOuterLoopIdx >>
                   /\ UNCHANGED << kStartingIdx, g_slots, g_idx, 
                                   hWriterMaximumData, r_current, r_new_value, 
                                   r_data_read_i, r_local_data, 
                                   hReaderOuterLoopIdx, hReaderGotNewData, 
                                   hReaderMaximumData, w_idx >>

WriterLoadIdx == /\ pc["writer"] = "WriterLoadIdx"
                 /\ w_idx' = g_idx.idx
                 /\ g_idx' = [g_idx EXCEPT !.busy = TRUE]
                 /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteDataLoop"]
                 /\ UNCHANGED << kStartingIdx, g_slots, hWriterMaximumData, 
                                 r_current, r_new_value, r_data_read_i, 
                                 r_local_data, hReaderOuterLoopIdx, 
                                 hReaderGotNewData, hReaderMaximumData, 
                                 w_data_write_i, hWriterOuterLoopIdx >>

WriterWriteDataLoop == /\ pc["writer"] = "WriterWriteDataLoop"
                       /\ IF w_data_write_i <= kObjectSize
                             THEN /\ g_slots' = [g_slots EXCEPT ![w_idx][w_data_write_i] = hWriterMaximumData + 1]
                                  /\ w_data_write_i' = w_data_write_i + 1
                                  /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteDataLoop"]
                             ELSE /\ pc' = [pc EXCEPT !["writer"] = "WriterAfterWriteData"]
                                  /\ UNCHANGED << g_slots, w_data_write_i >>
                       /\ UNCHANGED << kStartingIdx, g_idx, hWriterMaximumData, 
                                       r_current, r_new_value, r_data_read_i, 
                                       r_local_data, hReaderOuterLoopIdx, 
                                       hReaderGotNewData, hReaderMaximumData, 
                                       w_idx, hWriterOuterLoopIdx >>

WriterAfterWriteData == /\ pc["writer"] = "WriterAfterWriteData"
                        /\ g_idx' = [g_idx EXCEPT !.busy = FALSE,
                                                  !.newdata = TRUE]
                        /\ hWriterMaximumData' = hWriterMaximumData + 1
                        /\ pc' = [pc EXCEPT !["writer"] = "WriterOuterLoop"]
                        /\ UNCHANGED << kStartingIdx, g_slots, r_current, 
                                        r_new_value, r_data_read_i, 
                                        r_local_data, hReaderOuterLoopIdx, 
                                        hReaderGotNewData, hReaderMaximumData, 
                                        w_idx, w_data_write_i, 
                                        hWriterOuterLoopIdx >>

writer == WriterOuterLoop \/ WriterLoadIdx \/ WriterWriteDataLoop
             \/ WriterAfterWriteData

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

====
