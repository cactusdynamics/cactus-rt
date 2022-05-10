=================
``mutex_example``
=================

This program shows the usage of sharing data between an RT and a non-RT thread
via the ``rt::mutex``, which the library presented in this repository
implements via a priority-inheriting pthread mutex.

Specifically, this example implements a very naive double buffer. This data
structure has 2 data slots guarded by the priority-inheriting mutex. The RT
thread writes to the double buffer at 1 kHz and the non-RT thread reads it
every 500ms. Once it is read, it is displayed in the console.

To run:

.. code-block:: console

   $ sudo build/examples/mutex_example/rt_mutex_example

You should be able to see 4 values changing every 0.5s, and they are:

#. The elapsed time in nanoseconds.
#. The elapsed time in microseconds.
#. The output of the cosine function (amplitude = 1, period = 5 seconds).
#. The output of the cosine function times 10.

These 4 values are written by the RT thread into the double buffer and read
from the non-RT thread from the double buffer live, so you should see the third
column go from 1 -> -1 -> 1 every 5 seconds.

Todo:

* Ensure that mutex unlock is RT safe. This can call a syscall and need to make
  sure this syscall can't block on Linux.
* Demonstrate priority inversion with ``std::mutex`` by tracing with
  ``ftrace``.
