`ros2` examples
===============

This directory contains many examples showing how to use the various ROS2
integration feature of cactus-rt. The most important is the ability to receive
and publish ROS2 messages.

In general, ROS 2 data structure are not safe to construct and copy in
real-time due to the internal usage of data structures like `std::vector` which
can result in memory allocation in the constructors. As a result, [ROS2 type
adaptation](https://ros.org/reps/rep-2007.html) is used to adapt the ROS types
into real-time-safe versions that you must define for your application. These
are shown in the `complex_data.cc` examples for the
[publisher](publisher/complex_data.cc) and
[subscriber](subscriber/complex_data.cc). However, these type adaptaion triggers
an extra copy in the non-real-time thread which can limit throughput.

In some situation, the ROS type is actually real-time-safe. In these situations,
type adaptation can be turned off via an extra template argument (required as
ROS-generated types typically create non-trivial constructors which makes it
difficult for us to detect the type is a
[POD](https://en.cppreference.com/w/cpp/types/is_pod)). Turning off type
adaptation results in one less copy in the non-real-time thread, potentially
increasing throughput. These are shown in the `simple_data.cc` examples for the
[publisher](publisher/simple_data.cc) and
[subscriber](subscriber/simple_data.cc). **This should be used sparingly as most
ROS types are not real-time safe. If you turn off type adaptation and the
underlying ROS data incurs memory allocation on construction/copy, the cactus-rt
code path will not be real-time-safe.**

Differences from ROS
--------------------

ROS subscribers are callbacks that executes on message arrival. ROS publishers
are simple function calls that writes the data directly to the middleware (which
internally may have buffering and async behaviors). The ROS integration for
cactus-rt does not work like this. Instead:

- Subscription messages must be polled on each iteration of the real-time loop.
- Messages published from the real-time thread is queued and sent to ROS in
  batches by a non-real-time thread.

This means messages received by the real-time thread will be slightly delayed
according to the real-time loop frequency. Published messages are also slightly
delayed as it is processed in the background. These trade offs are made to keep
the real-time loop within hard deadlines, instead of ensuring messages are
delivered as fast as possible.

Subscriber
----------

There are two ways to subscribe data from a real-time thread:

- `CreateSubscriptionForLatestValue`: this will only allow the real-time thread
  to read the latest message from the subscription. If multiple messages are
  received between consecutive reads by the real-time thread, the latest value
  is the only one that is available. This is shown in
  [`simple_data.cc`](subscriber/simple_data.cc) and
  [`complex_data.cc`](subscriber/complex_data.cc).
- `CreateSubscriptionQueued`: this will allow the real-time thread to read all
  messages from the subscription, up to the queue size limit. The real-time
  thread will also get these messages in a FIFO order. If the queue size limits
  are reached, messages will be dropped when being received.

Conceptually, the LatestValue variant is a queue with a size of 1. Many robotics
applications should work with this, as many applications simply require the
latest value. An example is a goal pose. The real-time thread is almost always
only interested in the latest goal pose.

Publisher
---------

Messages published from the real-time thread are batch processed in a
non-real-time thread (`Ros2Adapter::TimerCallback`). This means data might be
slightly delayed. Depending on the QoS setting of the receive side, there could
also be message drops at the receive side if messages are published at high
frequencies (~1000 Hz).
