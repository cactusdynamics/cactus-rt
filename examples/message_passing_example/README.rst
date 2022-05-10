===========================
``message_passing_example``
===========================

This example is a more "complete" example compared to others, and it is a
simplified version of what a more "real" program would look like. There are two
threads:

* ``DataLogger``: a non RT thread that receives data and logs the data into a
  CSV file every 1 second.
* ``RtThread``: a RT ``CyclicFifoThread`` that executes at 1 kHz. For
  demonstration purposes, it simply calculates a cosine function (amplitude =
  1, period = 1 second). The output of the cosine function is sent to the
  ``DataLogger``.

The data is sent from the ``RtThread`` to the ``DataLogger`` via a
``boost::lockfree::spsc_queue``, which is a single-producer-single-consumer
queue that is a lock-free ring buffer. When the data in this queue is full, the
data is discarded and a failed push count is incremented. When the queue is
empty, nothing is returned when popping it. See the `docs
<https://www.boost.org/doc/libs/1_56_0/doc/html/boost/lockfree/spsc_queue.html>`__
for more details. The capacity of the queue is determined to be 8 * 1024, which
is good enough for >8 seconds of data, as the RT thread runs at 1 kHz.

The data is read by the ``DataLogger`` almost continuously and placed in a
buffer (a ``std::vector``). Every second, it will append the data to a CSV file
and empty/reset the buffer. At the end of the program, it will empty the buffer
and write all remaining data into the CSV one final time.

This design emulates a real-world program where the RT thread is doing work and
needs to log metrics in a RT-safe manner.
