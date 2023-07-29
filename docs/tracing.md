Real-time tracing
=================

Real-time applications are characterized by their ability to execute code within
a specific amount of time. To verify that the application is indeed "real-time
compliant", it is important to collect and analyze data about the timing of code
execution. This is known as [tracing][1], where information and timing about the
program execution is logged in a specialized manner such that it can be
visualized later.

[1]: https://en.wikipedia.org/wiki/Tracing_(software)

For real-time purposes, the most important data to collect is the time duration
of certain blocks of code. This information can then be visualized on a
timeline, or analyzed statistically (such as via mean, average, min, max, and
percentile analysis), to experimentally determine whether or not an application
conforms to its deadline requirements. This benchmark/validation step is very
important during the development of a real-time application.

To make things more concrete, consider an example where a loop controlling a
robot is executing in real time at 1000 Hz. Suppose the each iteration of the
loop consists of the following three sequential actions:

1. `Sense`
2. `Plan`
3. `Act`

The sum of the duration of these actions must not exceed 1 ms (as the loop is
1000 Hz). Considering other overheads (such as operating system scheduling
latency) and safety margin, a real-world design constraint may limit the sum of
the duration to maybe 0.5ms or less. It is important to collect data from
real-program execution and verify that the application timing indeed conforms to
the specification.

To accomplish this verification without a proper tracing system, one may be
tempted to write code similar to this:

```c++
void Loop() {
  auto t1 = NowNs();
  Sense();
  auto t2 = NowNs();
  Plan();
  auto t3 = NowNs();
  Act();
  auto t4 = NowNs();

  auto sense_duration = t2 - t1;
  auto plan_duration = t3 - t2;
  auto act_duration = t4 - t3;
  auto loop_duration = t4 - t1;
  CollectTiming(sense_duration, plan_duration, act_duration, loop_duration);
}
```

Since this code is supposed to execute in real-time, we have to assume that
`CollectTiming` is real-time compliant and is therefore likely to be slightly
complex (how this would be done is left as an exercise for the reader). After
the timing information is collected, it must be manually analyzed and visualized
(either in spreadsheets or via scripts). This is all very tedious and error
prone.

Fortunately, cactus_rt is built with a real-time-compliant tracing system where
you can instead write your code as follows:

```c++
void Sense() {
  auto span = Tracer()->WithSpan("Sense");
  // Your custom code...
}

void Plan() {
  auto span = Tracer()->WithSpan("Plan");
  // Your custom code...
}

void Act() {
  auto span = Tracer()->WithSpan("Act");
  // Your custom code...
}

void Loop() {
  Sense();
  Plan();
  Act();
}
```

It then generates a file that can be imported into an offline (not dependent on
a remote server) Web UI where the following interactive timeline plot can be
generated:

...

From the same WebUI, we can run SQL queries to analyze the data:

...

Custom tools can also be written to further analyze this data:

...

How to use
----------

How it works
------------

### Perfetto

### Real-time data flow

### Performance and limitations

Advanced tuning and use cases
-----------------------------

