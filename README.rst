==========================================
cactus-rt: a Linux real-time app framework
==========================================

Relevant blog posts: `Part 1 <https://shuhaowu.com/blog/2022/01-linux-rt-appdev-part1.html>`__ | `Part 2 <https://shuhaowu.com/blog/2022/02-linux-rt-appdev-part2.html>`__ | `Part 3 <https://shuhaowu.com/blog/2022/03-linux-rt-appdev-part3.html>`__ | `Part 4 <https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html>`__

---------------------
``cactus_rt`` library
---------------------

This is a library that refactors a lot of the boilerplate code needed for
writing a real-time Linux application. Some key features are:

* ``cactus_rt::App``: Implements logic for memory locking, memory reservation, and
  ``malloc`` tuning.

  * The memory reservation and ``malloc`` tuning may not be needed if an O(1)
    allocator is not used. See `this discussion
    <https://github.com/ros-realtime/ros2-realtime-examples/issues/9>`__.

* ``cactus_rt::Thread``: Implements a thread class that can be inherited to setup
  both RT and non-RT threads.
* ``cactus_rt::CyclicFifoThread``: Implements a RT thread with ``SCHED_FIFO`` with
  looping code builtin.

  * For applications with extra low-jitter requirements, it implements a busy
    wait method to reduce wakeup jitter. See `this
    <https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html#trick-to-deal-with-wake-up-jitter>`__
    for more details.
  * Tracks statistics for wakeup, iteration, and (if applicable) busy-wait
    latency online.
  * In the future: may implement built-in support for LTTNG-UST and/or USDT
    tracing.

* ``cactus_rt::mutex``: A priority-inheriting mutex that is a drop-in replacement for
  ``std::mutex``.

* Some work in progress and future work:

  * Using `TLA+ <https://en.wikipedia.org/wiki/TLA%2B>`__ to formally analyze
    several lock-less message passing techniques to pass data from RT to non-RT
    and vice versa. Based on the `farbot <https://github.com/hogliux/farbot>`__
    project.
  * Implementing ``cactus_rt::CyclicDeadlineThread``, which is RT looping with the
    ``SCHED_DEADLINE`` scheduler.

--------
Examples
--------

See each example's README for more details on what they do.

* |simple_example|_: shows a no-op application with a single RT
  ``CyclicFifoThread``. Also shows how to pin the RT thread onto a CPU via
  ``cpu_affinity``.
* |mutex_example|_: shows the usage of the ``cactus_rt::mutex``, which is a
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

To build in debug mode:

.. code-block:: console

   $ make debug

To run an example:

.. code-block:: console

   $ sudo build/debug/examples/simple_example/rt_simple_example

To turn on ``clang-tidy``:

.. code-block:: console

   $ make debug ENABLE_CLANG_TIDY=ON

For compiling in release mode:

.. code-block:: console

   $ make release

All flags remain valid for both ``make debug`` and ``make release``. Consult
the ``Makefile`` for details on how it works as it is just a convenience
wrapper on cmake. The example binaries will be located in the folder
``build/release`` instead of ``build/debug``.

To turn OFF building the examples:

.. code-block:: console

   $ make debug ENABLE_EXAMPLES=OFF

To build into other projects, simply use ``FetchContent`` in your
``CMakeLists.txt`` file:

.. code-block:: cmake

   include(FetchContent)
   FetchContent_Declare(
     cactus_rt
     GIT_REPOSITORY https://github.com/cactusdynamics/cactus-rt.git
     GIT_TAG        ...
   )
   FetchContent_MakeAvailable(cactus_rt)

   # ...

   target_link_libraries(myapp PRIVATE cactus_rt)

Note that if you compile your app in debug mode, cactus-rt will be compiled in
debug mode due to how ``FetchContent`` works. To get cactus-rt in release mode,
compile your app in release mode.

For testing like CI, you need docker installed and then you can use:

.. code-block:: console

   $ scripts/test-in-docker

-------
LICENSE
-------

Open source projects and some commercial projects can use `MPL 2.0
<https://www.mozilla.org/MPL/2.0/>`__.

If you need commercial, closed-sourced modifications, please obtain a license
from `Cactus Dynamics <https://cactusdynamics.com>`__.
