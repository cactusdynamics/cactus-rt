cactus-rt: a Linux real-time app framework
==========================================

Relevant blog posts: [Part 1](https://shuhaowu.com/blog/2022/01-linux-rt-appdev-part1.html) | [Part 2](https://shuhaowu.com/blog/2022/02-linux-rt-appdev-part2.html) | [Part 3](https://shuhaowu.com/blog/2022/03-linux-rt-appdev-part3.html) | [Part 4](https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html)

`cactus_rt` library
-------------------

This is a library that refactors a lot of the boilerplate code needed for
writing a real-time Linux application. Some key features are:

* `cactus_rt::App`: Implements logic for memory locking, memory reservation, and
  `malloc` tuning.
  * The memory reservation and `malloc` tuning may not be needed if an O(1)
    allocator is not used. See [this discussion](https://github.com/ros-realtime/ros2-realtime-examples/issues/9>).
* `cactus_rt::Thread<SchedulerT>`: Implements a thread class. Applications are
  expected to create a derived class for their custom threads. The `SchedulerT`
  template argument specifies the scheduler class the thread can use. Right now,
  `cactus_rt::schedulers::Fifo`, `cactus_rt::schedulers::Deadline`, and
  `cactus_rt::schedulers::Other` (non-RT) can be used.
* `cactus_rt::CyclicThread<SchedulerT>`: Implements a looping thread.
  * For applications with extra low-jitter requirements, it implements a busy
    wait method to reduce wakeup jitter. See [this](https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html#trick-to-deal-with-wake-up-jitter)
    for more details. In the future, this will be a scheduler
    (`cactus_rt::schedulers::FifoBusyWait`) but it is not yet implemented.
* `cactus_rt::mutex`: A priority-inheriting mutex that is a drop-in replacement
  for `std::mutex`.

Examples
--------

Core examples that show you how to use all the facilities of cactus-rt:

* [`simple_example`](examples/simple_example/): The most basic example showing
  a single real-time looping thread running at 1000 Hz.
* [`tracing_example`](examples/tracing_example/): This demonstrates how to use
  the real-time-safe tracing system built into cactus-rt. This is probably a
  good thing to undrestand immediately after the above example.
* [`mutex_example`](examples/mutex_example/): Demonstrates the usage of
  priority-inheritence mutex (`cactus_rt::mutex`) to pass data between real-time
  and non-real-time threads via the implementation of a mutex-based double
  buffer.
* [`lockless_examples`](examples/lockless_examples/): Demonstrates the usage of
  lockless data structures built into cactus-rt to safely pass data to and from
  the real-time thread.
* [`logging_example`](examples/logging_example/): Demonstrates setting up custom
  logging configuration via `cactus_rt::App`.
* [`message_passing_example`](examples/message_passing_example/): A simplified
  example of a real robotics application consists of two threads: a real-time
  thread that is generating metrics and a non-real-time data logger that logs
  the metrics to disk.
* [`ros2`](examples/ros2/): Shows how to use cactus-rt with ROS2.

Some examples showing optional/advanced features/usage patterns of cactus-rt.

* [`simple_deadline_example`](examples/simple_deadline_example/): Same as
  `simple_example`, except it uses `SCHED_DEADLINE` as opposed to `SCHED_FIFO`.
  This is for a more advanced use case.
* [`random_example`](examples/random_example/): Shows you how to use cactus-rt's
  real-time-safe random number generator.
* [`tracing_example_no_rt`](examples/tracing_example_no_rt/): Shows how to using
  the tracing library in `cactus_rt` without using `cactus_rt::App`.


Installation instructions
-------------------------

### Dependencies

`cactus_rt` the library is dependent on:

* Linux
  * `PREEMPT_RT` patch preferred, but not required as mainline Linux has partial
    real-time support (with higher latency).
* C++ compiler supporting C++ 17 and up.
* CMake
* [Quill](https://github.com/odygrd/quill): this is included as a part of the CMake-based build process.
* [`moodycamel::ReaderWriterQueue`](https://github.com/cameron314/readerwriterqueue): this is included as a part of the CMake-based build process.
* Protobuf: for runtime tracing
* GTest (libgtest-dev), Google Benchmark (libbenchmark-dev): for testing and benchmarking

For Debian/Ubuntu:

```bash
$ sudo apt install build-essential cmake protobuf-compiler libprotobuf-dev libgtest-dev libbenchmark-dev
```

For building documentations, we need: doxygen.

### Build

To build in debug mode:

```bash
$ make debug
```

To run an example:

```bash
$ sudo build/debug/examples/simple_example/rt_simple_example
```

To turn OFF building the examples:

```bash
$ make debug ENABLE_EXAMPLES=OFF
```

To turn on `clang-tidy`:

```bash
$ make debug ENABLE_CLANG_TIDY=ON
```

For compiling in release mode:

```bash
$ make release
```

All flags remain valid for both `make debug` and `make release`. Consult
the `Makefile` for details on how it works as it is just a convenience
wrapper on cmake. The example binaries will be located in the folder
`build/release` instead of `build/debug`.

For testing like CI, you need docker installed and then you can use:

```bash
$ scripts/test-in-docker
```

### Include from another project

To build into other projects, simply use `FetchContent` in your
`CMakeLists.txt` file:

```cmake
include(FetchContent)
FetchContent_Declare(
  cactus_rt
  GIT_REPOSITORY https://github.com/cactusdynamics/cactus-rt.git
  GIT_TAG        ...
)
FetchContent_MakeAvailable(cactus_rt)

# ...

target_link_libraries(myapp PRIVATE cactus_rt)
```

Note that if you compile your app in debug mode, cactus-rt will be compiled in
debug mode due to how `FetchContent` works. To get cactus-rt in release mode,
compile your app in release mode.

LICENSE
-------

Open source projects and some commercial projects can use [MPL 2.0](https://www.mozilla.org/MPL/2.0/).

If you need commercial, closed-sourced modifications, please obtain a license from [Cactus Dynamics](https://cactusdynamics.com).

This library embeds work from [Perfetto](https://perfetto.dev), which is licensed under Apache License, version 2.
