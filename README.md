cactus-rt: a Linux real-time app framework
==========================================

Relevant blog posts: [Part 1](https://shuhaowu.com/blog/2022/01-linux-rt-appdev-part1.html) | [Part 2](https://shuhaowu.com/blog/2022/02-linux-rt-appdev-part2.html) | [Part 3](https://shuhaowu.com/blog/2022/03-linux-rt-appdev-part3.html) | [Part 4](https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html)

Developing real-time applications is already difficult due to the need to
validate all parts of the system from hardware to the application. On a
general-purpose operating system such as Linux, the complexity increases further
due to most APIs being optimized for throughput as opposed to maximum latency.

cactus-rt is a C++ library that aims to make writing real-time Linux
applications as easy as writing Arduino programs. Real-time application
developers simply have to fill out a `Loop` function achieve 1000 Hz on Linux.
The library should make most of the tedious decisions for you and provide sane defaults for everything.

How?
----

### Core library

The core of cactus-rt consists of code that wraps the underlying OS-level
real-time APIs so your application do not have to call them manually. These
components includes:

- `cactus_rt::App`: memory locking, malloc tuning, service thread creation.
- `cactus_rt::Thread`: pthreads API for real-time thread creation
- `cactus_rt::CyclicThread`: real-time-safe clock to implement real-time timer
- `signal_handler`: handle signals

These are the bare minimum needed to create a real-time application. The
interface is simple enough that all the application developer needs to do is to
fill out `Loop` methods on classes derived from `CyclicThread`.

Example (full example in [examples/simple_example](examples/simple_example/)):

```c++
class ExampleRTThread : public cactus_rt::CyclicThread {
 public:
  ExampleRTThread() : CyclicThread("ExampleRTThread", MakeConfig()) {}

 protected:
  LoopControl Loop(int64_t elapsed_ns) noexcept final {
    // Your code here...
    return LoopControl::Continue;
  }

  // ... MakeConfig definition omitted
};

```

### Asynchronous logging integration via [Quill][quill]

Debugging logic bugs in real-time applications during development can be tedious
as logging via STL logging facilities (`std::cout`, `std::print`) are not
real-time-safe in general. To get around this problem, cactus-rt natively
integrates with [Quill][quill], which is an asynchronous, lock-free, and
allocation-free logging library that also allows for simple usability with
template strings. cactus-rt sets up Quill to run in non-allocating mode which is
safe for real-time usage.

Since printf debugging is a critical feature to debug during development (and
beyond), having Quill integrated directly in cactus-rt makes debugging real-time
applications as easy as normal applications.

Example (full example in [examples/simple_example](examples/simple_example/)):

```c++
LoopControl Loop(int64_t elapsed_ns) noexcept final {
  LOG_INFO(Logger(), "Hello {} {}", "world", 123); // Hello world 123
  return LoopControl::Continue;
}
```

[quill]: https://github.com/odygrd/quill

### Runtime performance tracing and visualization

Debugging timing bugs in real-time applications is critical as missed deadlines
can have catastrophic consequences. One of the design goal of this library is to
make debugging timing problems as easy as printf debugging. To accomplish this,
cactus-rt includes a real-time-safe tracing system (implemented in a lock-free
and allocation-free manner) that can measure the timing of spans within the
code.

This system is designed to be safe to run for real-time application in
production, as many timing issues can only be debugged within production. For
certain applications, the entire run session can theoretically be traced to
enable detailed analysis in post.

Example (full example in [examples/tracing_example](examples/tracing_example/)):

```c++
void Plan noexcept {
  // span will use RAII to emit a start and end event to be used for visualization
  // For this span, it would be the duration of this function
  auto span = Tracer().WithSpan("Plan");
  // ... your code
}
```

The tracing system emits data in [Perfetto][perfetto]-compatible format.
Perfetto has likely the best tracing visualization and analysis system in the
world. All you need to do is load up the generated trace file in a web UI
(hosted on https://cactusdynamics.github.io/perfetto or https://ui.perfetto.dev;
the analysis UI is entirely client side so no data is uploaded to any servers)
the above code looks like the following in Perfetto:

<img src=docs/imgs/perfetto1.png />

You can also use SQL and [Vega-Lite](https://vega.github.io/vega-lite/) to
further analyze your data. For more information, see [the tracing
document](docs/tracing.md).

With this system in place, debugging timing issues for real-time applications
becomes as simple as loading up a web UI.

[perfetto]: https://perfetto.dev/

### Native [ROS 2][ros2] support

Many real-time applications are written for robotics applications where
interaction with ROS 2 is required. cactus-rt provides builtin support to publish
and subscribe to ROS 2 topics from the real-time thread with a simple API. This
API is designed to allow information to be passed to and from the real-time
thread without impacting the real-time thread's maximum latency. An example use
case maybe passing a goal pose to a real-time thread from ROS 2 and passing
robot metrics collected by the real-time thread to ROS 2.

Example (full examples in [examples/ros2](examples/ros2/)):

```c++
LoopControl Loop(int64_t elapsed_ns) noexcept final {
  StampedValue<Velocity2D> msg = cmd_vel_sub_->ReadLatest();

  Velocity2D achieved_velocity = Drive(msg.value.vx, msg.value.vy, msg.value.w);
  feedback_pub_->Publish(achieved_velocity);

  return LoopControl::Continue;
}
```

This significantly simplifies real-time robotics application development with ROS 2.

[ros2]: https://ros.org/

### Real-time-safe inter-thread communication

Passing messages between real-time and non-real-time threads is very common use
case in real-time applications.  Yet, it is quite difficult to do this in a
real-time-safe manner. The simplest method, `std::mutex` is not even usable due
to [priority inversion](https://en.wikipedia.org/wiki/Priority_inversion).
cactus-rt solves this with a few different (yet non-exhaustive) approaches:

- The inclusion of `cactus_rt::mutex` which is a mutex that respects priority inheritance.
- Lockless data structures that allows for a single value to be shared between a
  single non-real-time and a single real-time-thread under
  `cactus_rt::experimental::lockless`.
  - Some of these algorithms are developed by [Dave Rowland and Fabien Renn-Giles](https://www.youtube.com/watch?v=PoZAo2Vikbo). We also formally analyzed these algorithms with [TLA+](tla) which gives high confidence of their correctness.

Further, cactus-rt extensively uses and therefore links to
[`moodycamel::readerwriterqueue`](https://github.com/cameron314/readerwriterqueue),
which is a SPSC lockless, allocation-free queue. This can also solve a number of
communication problems.

The integration of inter-thread communication APIs is designed to make life
easier as then developers no longer have to manually implement or include
libraries that do the same thing.

### Others and future work

There are some other utilities in cactus-rt other than the above, and there are always more ideas to allow for simpler real-time application development.


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

Open source projects and some commercial projects can use [MPL 2.0](https://www.mozilla.org/MPL/2.0/). Please note the license's section 6 and 7 where it is noted that the software is provided "as is" and is not liable for any damages (the license text supersedes this excerpt).

If you need commercial, closed-sourced modifications, please obtain a license from [Cactus Dynamics](https://cactusdynamics.com).

This library embeds work from [Perfetto](https://perfetto.dev), which is licensed under Apache License, version 2.
