Notes on lock-free queues
=========================

Tracing
-------

For tracing, the real-time thread is supposed to pass tracepoint information to
a non-real-time thread who aggregates them and emits the trace events to
disk/network/whatever. Much like [logging](logging.md), this information passing
should not block, allocate, or use mutexes to ensure real-time behavior.

### Wait-free queue

We need a wait-free queue to pass data from the real-time thread to the
non-real-time thread:

- **Wait-free SPSC**: SPSC is simplest to implement. Quill uses this approach to
  get logs from the real-time thread to the non-real-time thread. The background
  thread reads from all SPSC queues and merge them after performing a sort based
  on system clock. This approach is fine for tracing as well thus a SPSC queue
  is sufficient.
- **Nonblocking on push**: Since the trace data is pushed from the real-time
  thread, this code path can never block and should ideally be wait-free.
- **Non-allocating on push**: On push, memory allocation must not be called. If
  this means if there are too much trace data going to the queue, we have to
  drop the trace information, which is acceptable. We can increment a
  thread-local atomic counter that reports this issue to the background thread.
- **Ideally zero-copy**: The trace data should be passed to the queue ideally in
  a zero-copy manner to minimize latency.
- **Easy to use**: Ideally the queue should be easy to use, and applications
  written with cactus-rt can use the same queue if they need something similar.
- **Well supported and maintained**: since we do not want to maintain our own
  SPSC queue implementation for this, the selected library should be well
  maintained and well supported by upstream.

The following queues were evaluated:

| Library | Non-blocking on push | Non-allocating | Zero-copy | Easy of use | Maintenance | Notes |
|---------|----------------------|----------------|-----------|-------------|-------------|-------|
| [`boost::lockless::spsc`][boost-spsc] | Yes | Yes | No | Good | Meh | |
| [`readerwriterqueue`][readerwriterqueue] | Yes | Yes (`try_enqueue` and `try_emplace` only) | Yes | Good | Good? | Has a version that's blocking for pop using `sem_wait` and `sem_post`, which internally uses a futex which cannot be used in real time? Need to see what `futex_wait` does... [^1]; Has an exception-free version based on compile definition; |
| [`SPSCQueue`][rigtorp-spsc] | Yes (`try_enqueue` and `try_emplace` only) | ? | Yes | Good | ?  | |
| [`ProducerConsumerQueue`][folly-producerconsumer] | Yes | Yes | ? | Meh | Good? | Facebook maintains this as a part of a larger library which might be annoying to pull |
| [Quill-internal bounded queue][quill-queue] | Yes? | Yes? | Yes? | Bad | Good | This is an internal implementation specific for the Quill logging library. While it would be nice to be able to reuse this queue to minimize the amount of dependencies, this might not realistically realistic. |

[boost-spsc]: https://www.boost.org/doc/libs/1_78_0/doc/html/boost/lockfree/spsc_queue.html
[readerwriterqueue]: https://github.com/cameron314/readerwriterqueue
[rigtorp-spsc]: https://github.com/rigtorp/SPSCQueue
[folly-producerconsumer]: https://github.com/facebook/folly/blob/main/folly/docs/ProducerConsumerQueue.md
[quill-queue]: https://github.com/odygrd/quill/blob/v3.1.0/quill/include/quill/detail/spsc_queue/BoundedQueue.h

The best option from the above appears to be the the [`readerwriterqueue`][readerwriterqueue].

[^1]: More information about FUTEX_WAKE is found in this blog post's comments: https://timur.audio/using-locks-in-real-time-audio-processing-safely

### Data-passing architecture

### Trace data format

### Trace viewing
