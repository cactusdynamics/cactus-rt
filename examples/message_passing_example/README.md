`message_passing_example`
=========================

This example is a more "complete" example compared to others, and it is a
simplified version of what a more "real" program would look like. There are two
threads:

- `DataLogger`: a non RT thread that receives data and logs the data into
  `build/data.csv` every 1 second.
- `RtThread`: a RT `CyclicThread` that executes at 1 kHz. For demonstration
  purposes, it simply calculates a cosine function (amplitude = 1, period = 1
  second). The output of the cosine function is sent to the `DataLogger``.

This demonstrates two kind of message passing: (1) message passing through a
single-producer-single-consumer (SPSC) queue and (2) message passing via an
`std::atomic`.

Message passing through SPSC queue
----------------------------------

This is akin to streaming robotics data from a real-time control thread to a
non-real-time data logger thread so the robotics data can be saved to disk. In
this example, an `OutputData` struct is sent from the `RtThread` to the
`DataLogger` thread via the [`moodycamel::readerwriterqueue`][moodycamel],
which is a queue cactus-rt links to by default (so there's no "external
dependencies"). This is a single-producer-single-consumer queue that's wait-free
when using the `try_emplace` and `try_push` methods, which makes it suitable for
real time. The `RtThread` is running at 1 kHz and sends one such structure per
iteration, mimicking what would happen in a real-world robot controller code.
The `RtThread` is rigged to run for 30 seconds. Once the `RtThread` quits, the
entire program quits.

The data is read by the `DataLogger` almost continuously and placed into a
temporary buffer (backed by a `std::vector` that has pre-allocated a certain
amount of space). Every 1 second, it flushes the buffer to a CSV file located at
**`build/data.csv`**. It will also flush and write the buffer content when it
*terminates.

As noted, this emulates a real-world application where the RT thread is doing
work and needs to log per-iteration metric to a data logger in a real-time-safe
manner. In fact, any time you need to send ordered messages from a RT thread to
a non-RT thread, you can use a similar pattern.

[moodycamel]: https://github.com/cameron314/readerwriterqueue

Message passing through `std::atomic`
-------------------------------------

A second example of message passing through `std::atomic` is shown via the
message counter (`DataLogger.message_count_`).

TODO: write more about this case...
