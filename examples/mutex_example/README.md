`mutex_example`
===============

This program shows the usage of sharing data between an RT and a non-RT thread
via the `cactus_rt::mutex`, which is a priority-inheritence mutex compatible
with the [`Lockable`](https://en.cppreference.com/w/cpp/named_req/Lockable)
interface.

Specifically, this example implements a very naive double buffer. This data
structure has 2 data slots guarded by the priority-inheriting mutex. The RT
thread writes to the double buffer at 1 kHz and the non-RT thread reads it every
half second. Once it is read, it is logged via the `cactus_rt` logging
capability.

To run:

```bash
$ make debug
$ sudo build/debug/examples/mutex_example/rt_mutex_example
```

You should be able to see 4 values changing every 0.5s, and they are:

1. The elapsed time in nanoseconds.
2. The elapsed time in microseconds.
3. The output of the cosine function (amplitude = 1, period = 5 seconds).
4. The output of the cosine function times 10.

These 4 values are written by the RT thread into the double buffer and read from
the non-RT thread from the double buffer live, so you should see the third
column go from 1 -> -1 -> 1 every 5 seconds.
