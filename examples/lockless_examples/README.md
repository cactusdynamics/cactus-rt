Lockless examples
=================

`realtime_read`
---------------

This example shows you how to use the `RealtimeReadableValue` lockless data
structure. This data structure allows you to read a struct from a single
real-time thread in a wait-free manner O(1). The writer has to be a single
thread is non-real-time as the write algorithm is lock-free but not wait-free.
