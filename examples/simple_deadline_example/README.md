`simple_deadline_example`
=========================

The `SCHED_DEADLINE` scheduler is a more advanced scheduler but is still very
simple to use with Cactus-RT. In fact, it is almost identical to the looping
thread based on `SCHED_FIFO` as shown in [`simple_example`](../simple_example/).

See https://www.kernel.org/doc/html/latest/scheduler/sched-deadline.html for
more details on how to configure this scheduler for your application.

Note
----

CPU affinity currently cannot be used with SCHED_DEADLINE for unknown reasons.
Setting CPU affinity will cause `sched_setattrs` to fail with EPERM, which
results in an `Operation not permitted` error on startup of this example.

Also see: https://lwn.net/Articles/745626/
