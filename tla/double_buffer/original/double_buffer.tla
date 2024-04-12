------------------------ MODULE double_buffer ------------------------------

(***************************************************************************
This implements the double buffer algorithm originally introduced by Dave
Rowland and Fabien Renn-Giles in  Real-time 101 - Part II: The real-time
audio developer's toolbox (https://youtu.be/PoZAo2Vikbo?t=722).

The data here is modeled as a sequence of integer values. Everytime write
occurs, the integer values are incremented. This monotonic increasing makes
it easier to check that the data swaps are done properly.

This model also models multiple read/write iterations to catch problems
with multiple read/writes.

This is the wrong version to showcase that TLA+ can indeed catch problems.
Specifically this is the second wrong version that was introduced in the
presentation.
 ***************************************************************************)

EXTENDS Sequences, Integers, TLC, FiniteSets

(***************************************************************************
This is the size of the object. Each object has kObjectSize ObjectElements.

For modeling, it must be greater than 1.
 ***************************************************************************)
CONSTANT kObjectSize


CONSTANT kTotalIterationsCount

(***************************************************************************
This is just a model value for uninitialized data. Not super important.
 ***************************************************************************)
CONSTANT UninitializedElement

(***************************************************************************
Ways to create objects. Objects are sequences of multiple of the
same ObjectElements.
 ***************************************************************************)
ObjectWithValue(value) == [i \in 1..kObjectSize |-> value]

FlipIndex(i) == IF i = 1 THEN 2 ELSE 1

(* --algorithm double_buffer

variables
    g_slots = <<ObjectWithValue(1), ObjectWithValue(0)>>, \* mostRecentSpectrum
    g_idx = [idx |-> 1, newdata |-> FALSE, busy |-> FALSE], \* the current index the writer should write to.
    g_writer_maximum_data = 1;

define
    DataIsNotTorn(data) == Cardinality({data[i] : i \in 1..kObjectSize}) = 1
end define;

fair process reader = "reader"
variables
    reader_outer_loop_idx = 1, \* Controls how many times we read in a row.
    reader_slot_idx, \* i in the original code
    reader_new_idx,
    reader_data_read_idx, \* the index of the read of the memory.
    reader_got_new_data,
    reader_local_data = ObjectWithValue(0), \* The data that is read by the reader thread.
    reader_maximum_data_tentative = 0,
    reader_maximum_data = 0;
begin
    ReaderOuterLoop:
        while reader_outer_loop_idx <= kTotalIterationsCount do
            reader_data_read_idx := 1; \* Reset this for the loop below.
            reader_outer_loop_idx := reader_outer_loop_idx + 1;
            reader_local_data := ObjectWithValue(0);
            reader_got_new_data := FALSE;

            ReaderLoadIndex:
                reader_slot_idx := g_idx;

            ReaderCheckNewData:
                if reader_slot_idx.newdata = TRUE then 
                    reader_slot_idx := [
                        idx |-> reader_slot_idx.idx, 
                        newdata |-> reader_slot_idx.newdata, 
                        busy |-> FALSE
                    ];
                    reader_new_idx := [
                        idx |-> FlipIndex(reader_slot_idx.idx),
                        newdata |-> FALSE,
                        busy |-> FALSE
                    ];
                    ReaderCAS:
                        if g_idx # reader_slot_idx then
                            reader_slot_idx := g_idx;
                            goto ReaderCheckNewData;
                        else
                            g_idx := reader_new_idx;
                            reader_slot_idx := reader_new_idx;

                            \* Below are accounting variables for assertions
                            reader_maximum_data_tentative := g_writer_maximum_data;
                            reader_got_new_data := TRUE;
                        end if;
                end if;

            ReaderReadDataLoop:
                while reader_data_read_idx <= kObjectSize do
                    \* Asserts no torn reads, as it's possible for the writer to write to the same slot if we don't assert.
                    assert DataIsNotTorn(g_slots[FlipIndex(reader_slot_idx.idx)]);

                    \* If we got new data, the data we are reading should be larger than the known maximum data as we are always incrementing forward.
                    assert
                        \/ ~reader_got_new_data
                        \/ g_slots[FlipIndex(reader_slot_idx.idx)][reader_data_read_idx] > reader_maximum_data;

                    reader_local_data[reader_data_read_idx] := g_slots[FlipIndex(reader_slot_idx.idx)][reader_data_read_idx];
                    reader_data_read_idx := reader_data_read_idx + 1;
                end while;

            ReaderAfterReadData:
                reader_maximum_data := reader_maximum_data_tentative; \* Keep accounting for TLC.

                \* Assert the data we read is not turn.
                assert DataIsNotTorn(reader_local_data);

                \* Assert the data we read is the data wrote at the time of the exchange index.
                assert reader_local_data = ObjectWithValue(reader_maximum_data)
        end while;
end process;

fair process writer = "writer"
variables
    writer_outer_loop_idx = 1,
    writer_slot_idx,
    writer_data_write_idx;
begin
    WriterOuterLoop:
        while writer_outer_loop_idx <= kTotalIterationsCount do
            writer_outer_loop_idx := writer_outer_loop_idx + 1;
            writer_data_write_idx := 1;

            WriterLoadIndex:
                writer_slot_idx := g_idx;
                g_idx.busy := TRUE;

            WriterWriteDataLoop:
                while writer_data_write_idx <= kObjectSize do
                    g_slots[writer_slot_idx.idx][writer_data_write_idx] := g_writer_maximum_data + 1;
                    writer_data_write_idx := writer_data_write_idx + 1;
                end while;

            WriterAfterWriteData:
                g_idx.busy := FALSE || g_idx.newdata := TRUE;
                g_writer_maximum_data := g_writer_maximum_data + 1;
        end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e7d07132" /\ chksum(tla) = "da8a2207")
CONSTANT defaultInitValue
VARIABLES g_slots, g_idx, g_writer_maximum_data, pc

(* define statement *)
DataIsNotTorn(data) == Cardinality({data[i] : i \in 1..kObjectSize}) = 1

VARIABLES reader_outer_loop_idx, reader_slot_idx, reader_new_idx, 
          reader_data_read_idx, reader_got_new_data, reader_local_data, 
          reader_maximum_data_tentative, reader_maximum_data, 
          writer_outer_loop_idx, writer_slot_idx, writer_data_write_idx

vars == << g_slots, g_idx, g_writer_maximum_data, pc, reader_outer_loop_idx, 
           reader_slot_idx, reader_new_idx, reader_data_read_idx, 
           reader_got_new_data, reader_local_data, 
           reader_maximum_data_tentative, reader_maximum_data, 
           writer_outer_loop_idx, writer_slot_idx, writer_data_write_idx >>

ProcSet == {"reader"} \cup {"writer"}

Init == (* Global variables *)
        /\ g_slots = <<ObjectWithValue(1), ObjectWithValue(0)>>
        /\ g_idx = [idx |-> 1, newdata |-> FALSE, busy |-> FALSE]
        /\ g_writer_maximum_data = 1
        (* Process reader *)
        /\ reader_outer_loop_idx = 1
        /\ reader_slot_idx = defaultInitValue
        /\ reader_new_idx = defaultInitValue
        /\ reader_data_read_idx = defaultInitValue
        /\ reader_got_new_data = defaultInitValue
        /\ reader_local_data = ObjectWithValue(0)
        /\ reader_maximum_data_tentative = 0
        /\ reader_maximum_data = 0
        (* Process writer *)
        /\ writer_outer_loop_idx = 1
        /\ writer_slot_idx = defaultInitValue
        /\ writer_data_write_idx = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "reader" -> "ReaderOuterLoop"
                                        [] self = "writer" -> "WriterOuterLoop"]

ReaderOuterLoop == /\ pc["reader"] = "ReaderOuterLoop"
                   /\ IF reader_outer_loop_idx <= kTotalIterationsCount
                         THEN /\ reader_data_read_idx' = 1
                              /\ reader_outer_loop_idx' = reader_outer_loop_idx + 1
                              /\ reader_local_data' = ObjectWithValue(0)
                              /\ reader_got_new_data' = FALSE
                              /\ pc' = [pc EXCEPT !["reader"] = "ReaderLoadIndex"]
                         ELSE /\ pc' = [pc EXCEPT !["reader"] = "Done"]
                              /\ UNCHANGED << reader_outer_loop_idx, 
                                              reader_data_read_idx, 
                                              reader_got_new_data, 
                                              reader_local_data >>
                   /\ UNCHANGED << g_slots, g_idx, g_writer_maximum_data, 
                                   reader_slot_idx, reader_new_idx, 
                                   reader_maximum_data_tentative, 
                                   reader_maximum_data, writer_outer_loop_idx, 
                                   writer_slot_idx, writer_data_write_idx >>

ReaderLoadIndex == /\ pc["reader"] = "ReaderLoadIndex"
                   /\ reader_slot_idx' = g_idx
                   /\ pc' = [pc EXCEPT !["reader"] = "ReaderCheckNewData"]
                   /\ UNCHANGED << g_slots, g_idx, g_writer_maximum_data, 
                                   reader_outer_loop_idx, reader_new_idx, 
                                   reader_data_read_idx, reader_got_new_data, 
                                   reader_local_data, 
                                   reader_maximum_data_tentative, 
                                   reader_maximum_data, writer_outer_loop_idx, 
                                   writer_slot_idx, writer_data_write_idx >>

ReaderCheckNewData == /\ pc["reader"] = "ReaderCheckNewData"
                      /\ IF reader_slot_idx.newdata = TRUE
                            THEN /\ reader_slot_idx' =                    [
                                                           idx |-> reader_slot_idx.idx,
                                                           newdata |-> reader_slot_idx.newdata,
                                                           busy |-> FALSE
                                                       ]
                                 /\ reader_new_idx' =                   [
                                                          idx |-> FlipIndex(reader_slot_idx'.idx),
                                                          newdata |-> FALSE,
                                                          busy |-> FALSE
                                                      ]
                                 /\ pc' = [pc EXCEPT !["reader"] = "ReaderCAS"]
                            ELSE /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadDataLoop"]
                                 /\ UNCHANGED << reader_slot_idx, 
                                                 reader_new_idx >>
                      /\ UNCHANGED << g_slots, g_idx, g_writer_maximum_data, 
                                      reader_outer_loop_idx, 
                                      reader_data_read_idx, 
                                      reader_got_new_data, reader_local_data, 
                                      reader_maximum_data_tentative, 
                                      reader_maximum_data, 
                                      writer_outer_loop_idx, writer_slot_idx, 
                                      writer_data_write_idx >>

ReaderCAS == /\ pc["reader"] = "ReaderCAS"
             /\ IF g_idx # reader_slot_idx
                   THEN /\ reader_slot_idx' = g_idx
                        /\ pc' = [pc EXCEPT !["reader"] = "ReaderCheckNewData"]
                        /\ UNCHANGED << g_idx, reader_got_new_data, 
                                        reader_maximum_data_tentative >>
                   ELSE /\ g_idx' = reader_new_idx
                        /\ reader_slot_idx' = reader_new_idx
                        /\ reader_maximum_data_tentative' = g_writer_maximum_data
                        /\ reader_got_new_data' = TRUE
                        /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadDataLoop"]
             /\ UNCHANGED << g_slots, g_writer_maximum_data, 
                             reader_outer_loop_idx, reader_new_idx, 
                             reader_data_read_idx, reader_local_data, 
                             reader_maximum_data, writer_outer_loop_idx, 
                             writer_slot_idx, writer_data_write_idx >>

ReaderReadDataLoop == /\ pc["reader"] = "ReaderReadDataLoop"
                      /\ IF reader_data_read_idx <= kObjectSize
                            THEN /\ Assert(DataIsNotTorn(g_slots[FlipIndex(reader_slot_idx.idx)]), 
                                           "Failure of assertion at line 106, column 21.")
                                 /\ Assert(\/ ~reader_got_new_data
                                           \/ g_slots[FlipIndex(reader_slot_idx.idx)][reader_data_read_idx] > reader_maximum_data, 
                                           "Failure of assertion at line 109, column 21.")
                                 /\ reader_local_data' = [reader_local_data EXCEPT ![reader_data_read_idx] = g_slots[FlipIndex(reader_slot_idx.idx)][reader_data_read_idx]]
                                 /\ reader_data_read_idx' = reader_data_read_idx + 1
                                 /\ pc' = [pc EXCEPT !["reader"] = "ReaderReadDataLoop"]
                            ELSE /\ pc' = [pc EXCEPT !["reader"] = "ReaderAfterReadData"]
                                 /\ UNCHANGED << reader_data_read_idx, 
                                                 reader_local_data >>
                      /\ UNCHANGED << g_slots, g_idx, g_writer_maximum_data, 
                                      reader_outer_loop_idx, reader_slot_idx, 
                                      reader_new_idx, reader_got_new_data, 
                                      reader_maximum_data_tentative, 
                                      reader_maximum_data, 
                                      writer_outer_loop_idx, writer_slot_idx, 
                                      writer_data_write_idx >>

ReaderAfterReadData == /\ pc["reader"] = "ReaderAfterReadData"
                       /\ reader_maximum_data' = reader_maximum_data_tentative
                       /\ Assert(DataIsNotTorn(reader_local_data), 
                                 "Failure of assertion at line 121, column 17.")
                       /\ Assert(reader_local_data = ObjectWithValue(reader_maximum_data'), 
                                 "Failure of assertion at line 124, column 17.")
                       /\ pc' = [pc EXCEPT !["reader"] = "ReaderOuterLoop"]
                       /\ UNCHANGED << g_slots, g_idx, g_writer_maximum_data, 
                                       reader_outer_loop_idx, reader_slot_idx, 
                                       reader_new_idx, reader_data_read_idx, 
                                       reader_got_new_data, reader_local_data, 
                                       reader_maximum_data_tentative, 
                                       writer_outer_loop_idx, writer_slot_idx, 
                                       writer_data_write_idx >>

reader == ReaderOuterLoop \/ ReaderLoadIndex \/ ReaderCheckNewData
             \/ ReaderCAS \/ ReaderReadDataLoop \/ ReaderAfterReadData

WriterOuterLoop == /\ pc["writer"] = "WriterOuterLoop"
                   /\ IF writer_outer_loop_idx <= kTotalIterationsCount
                         THEN /\ writer_outer_loop_idx' = writer_outer_loop_idx + 1
                              /\ writer_data_write_idx' = 1
                              /\ pc' = [pc EXCEPT !["writer"] = "WriterLoadIndex"]
                         ELSE /\ pc' = [pc EXCEPT !["writer"] = "Done"]
                              /\ UNCHANGED << writer_outer_loop_idx, 
                                              writer_data_write_idx >>
                   /\ UNCHANGED << g_slots, g_idx, g_writer_maximum_data, 
                                   reader_outer_loop_idx, reader_slot_idx, 
                                   reader_new_idx, reader_data_read_idx, 
                                   reader_got_new_data, reader_local_data, 
                                   reader_maximum_data_tentative, 
                                   reader_maximum_data, writer_slot_idx >>

WriterLoadIndex == /\ pc["writer"] = "WriterLoadIndex"
                   /\ writer_slot_idx' = g_idx
                   /\ g_idx' = [g_idx EXCEPT !.busy = TRUE]
                   /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteDataLoop"]
                   /\ UNCHANGED << g_slots, g_writer_maximum_data, 
                                   reader_outer_loop_idx, reader_slot_idx, 
                                   reader_new_idx, reader_data_read_idx, 
                                   reader_got_new_data, reader_local_data, 
                                   reader_maximum_data_tentative, 
                                   reader_maximum_data, writer_outer_loop_idx, 
                                   writer_data_write_idx >>

WriterWriteDataLoop == /\ pc["writer"] = "WriterWriteDataLoop"
                       /\ IF writer_data_write_idx <= kObjectSize
                             THEN /\ g_slots' = [g_slots EXCEPT ![writer_slot_idx.idx][writer_data_write_idx] = g_writer_maximum_data + 1]
                                  /\ writer_data_write_idx' = writer_data_write_idx + 1
                                  /\ pc' = [pc EXCEPT !["writer"] = "WriterWriteDataLoop"]
                             ELSE /\ pc' = [pc EXCEPT !["writer"] = "WriterAfterWriteData"]
                                  /\ UNCHANGED << g_slots, 
                                                  writer_data_write_idx >>
                       /\ UNCHANGED << g_idx, g_writer_maximum_data, 
                                       reader_outer_loop_idx, reader_slot_idx, 
                                       reader_new_idx, reader_data_read_idx, 
                                       reader_got_new_data, reader_local_data, 
                                       reader_maximum_data_tentative, 
                                       reader_maximum_data, 
                                       writer_outer_loop_idx, writer_slot_idx >>

WriterAfterWriteData == /\ pc["writer"] = "WriterAfterWriteData"
                        /\ g_idx' = [g_idx EXCEPT !.busy = FALSE,
                                                  !.newdata = TRUE]
                        /\ g_writer_maximum_data' = g_writer_maximum_data + 1
                        /\ pc' = [pc EXCEPT !["writer"] = "WriterOuterLoop"]
                        /\ UNCHANGED << g_slots, reader_outer_loop_idx, 
                                        reader_slot_idx, reader_new_idx, 
                                        reader_data_read_idx, 
                                        reader_got_new_data, reader_local_data, 
                                        reader_maximum_data_tentative, 
                                        reader_maximum_data, 
                                        writer_outer_loop_idx, writer_slot_idx, 
                                        writer_data_write_idx >>

writer == WriterOuterLoop \/ WriterLoadIndex \/ WriterWriteDataLoop
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

=============================================================================
\* Modification History
\* Last modified Thu Apr 04 19:46:55 EDT 2024 by shuhao
\* Created Wed Apr 03 20:06:15 EDT 2024 by shuhao
