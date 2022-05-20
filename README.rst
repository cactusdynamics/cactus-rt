================================
Real-time app framework and demo
================================

--------------
``rt`` library
--------------

This is a library that refactors a lot of the boilerplate code needed for
writing a real-time Linux application. Some key features are:

* ``rt::App``: Implements logic for memory locking, memory reservation, and
  ``malloc`` tuning.

  * The memory reservation and ``malloc`` tuning may not be needed if an O(1)
    allocator is not used. See `this discussion
    <https://github.com/ros-realtime/ros2-realtime-examples/issues/9>`__.

* ``rt::Thread``: Implements a thread class that can be inherited to setup
  both RT and non-RT threads.
* ``rt::CyclicFifoThread``: Implements a RT thread with ``SCHED_FIFO`` with
  looping code builtin.

  * For applications with extra low-jitter requirements, it implements a busy
    wait method to reduce wakeup jitter. See `this
    <https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html#trick-to-deal-with-wake-up-jitter>`__
    for more details.
  * Tracks statistics for wakeup, iteration, and (if applicable) busy-wait
    latency online.
  * In the future: may implement built-in support for LTTNG-UST and/or USDT
    tracing.

* ``rt::mutex``: A priority-inheriting mutex that is a drop-in replacement for
  ``std::mutex``.

* Some work in progress and future work:

  * Using `TLA+ <https://en.wikipedia.org/wiki/TLA%2B>`__ to formally analyze
    several lock-less message passing techniques to pass data from RT to non-RT
    and vice versa. Based on the `farbot <https://github.com/hogliux/farbot>`__
    project.
  * Implementing ``rt::CyclicDeadlineThread``, which is RT looping with the
    ``SCHED_DEADLINE`` scheduler.

--------
Examples
--------

See each example's README for more details on what they do.

* |simple_example|_: shows a no-op application with a single RT
  ``CyclicFifoThread``. Also shows how to pin the RT thread onto a CPU via
  ``cpu_affinity``.
* |mutex_example|_: shows the usage of the ``rt::mutex``, which is a
  priority-inheriting mutex that conforms to the same interface as
  ``std::mutex``, which allows it to be used with ``std::scoped_lock``. A naive
  double buffer is implemented with this mutex.
* |message_passing_example|_: shows a more complete application with a
  ``CyclicFifoThread`` computing a cosine function and outputting the data via
  a circular buffer (``boost::lockfree::spsc_queue``) to a data logger thread,
  which writes the data into a CSV file periodically.
* |lttng_ust_example|_: shows the no-op application but with `lttng-ust
  <https://lttng.org/docs/v2.13/#doc-c-application>`__ tracing the start and
  end of the loop.

.. |simple_example| replace:: ``simple_example``
.. _simple_example: examples/simple_example
.. |mutex_example| replace:: ``mutex_example``
.. _mutex_example: examples/mutex_example
.. |message_passing_example| replace:: ``message_passing_example``
.. _message_passing_example: examples/message_passing_example
.. |lttng_ust_example| replace:: ``lttng_ust_example``
.. _lttng_ust_example: examples/lttng_ust_example

------------
Dependencies
------------

Ubuntu/Debian
-------------

Tested on Debian 10 and Ubuntu 20.04:

.. code-block:: console

   $ sudo apt install libspdlog-dev liblttng-ust-dev libboost-dev lttng-tools

- ``liblttng-ust-dev`` is only used in ``lttng_ust_example``.
- ``lttng-tools`` is used for tracing the ``lttng_ust_example``.
- ``libboost-dev`` is only used for the lockfree queue in the ``message_passing_example``.

Of course you also need a C++ compiler and cmake.

-----
Build
-----

.. code-block:: console

   $ cmake -Bbuild
   $ cmake --build build -j $(nproc)

To turn on ``clang-tidy``:

.. code-block:: console

   $ cmake -Bbuild -DENABLE_CLANG_TIDY=ON
   $ cmake --build build -j $(nproc)

To turn OFF building the examples (for embedding into other projects):

.. code-block:: console

   $ cmake -Bbuild -DENABLE_EXAMPLES=OFF
   $ cmake --build build -j $(nproc)
