Real-time UDP under Linux
=========================

In some situations, it is important to communicate multiple devices over
ethernet network in soft real-time. While Ethernet and Linux (as well as the
PREEMPT_RT patch) are not designed for real-time communications, it remains
possible to achieve bounded latency with high probability ([1][1], [2][2]).

For simplicity, we assume communication is performed on a dedicated ethernet
link between two dedicated network interface controllers ([NICs][3]). We assume
that only the real-time processes are both sides are using these dedicated NICs
as well. We also assume the communication is done with IPv4. This is a very
restrictive environment that _should_ significantly reduce the risk of large
latency as there should be nothing else happening on this ethernet link other
than the desired real-time communication. We also assume that the real-time
applications on both side of the ethernet link only use one thread to
send/receive the data. Despite the restrictions, this remains to be a reasonably
practical example for smaller-scale robots where the real-time communication is
limited to two computer systems directedly connected to each other. For example,
one system could be transmitting a setpoint in real-time (at something like
200-500Hz) to another system that actually controls the motors.

To make things simpler further, we assume the send and receive network calls are
made once per real-time loop iteration. We assume this is done from a single
real-time thread that is correctly meeting its deadlines. We can further assume
that we are attempting to send this data at 500 Hz. We assume the systems should
only start sending data once they are ready (so a session needs to be
established). We assume the application can detect and tolerate a few missed
messages (up to some limit).

[1]: https://arxiv.org/pdf/1808.10821.pdf
[2]: https://ntrs.nasa.gov/api/citations/20200002393/downloads/20200002393.pdf
[3]: https://en.wikipedia.org/wiki/Network_interface_controller

The above assumption also implies a few additional things:

1. There is no need to implement encryption nor authentication as the ethernet
   link is assumed to be trusted.
2. Assume that the connection is only talking to a single host, so the receive
   from do not necessarily need to verify the sender IP address.
  - That said, we do want to perform an initial "handshake" just to ensure the
    server is up before blinding sending data down UDP, as there's no way to
    know the other side is up otherwise.

It may be possible to extend this to closed, multi-device networks. However, no
tests are conducted with this. This work has been tested with two Raspberry Pi
4s connected directly via Ethernet.

Design overview
---------------

### Application-side considerations

To increase determinism in such a setup requires the cooperation of the
application code and the kernel code. The send-side application is
responsible for serializing the data and sending it to the kernel via the socket
APIs (or perhaps more recent APIs such as `io_uring`). Similarly, the
receive-side application is responsible for receiving the data from the kernel
and deserializing them. Thus, we can break the application code into three
components:

1. It must serialize and deserialize data in a real-time-compliant manner. This
   means it must be lock-free and allocation-free.
2. The interaction with the kernel APIs must also be done in a lock-free and
   allocation-free manner.
3. A basic protocol is needed so that a simple session can be established and we
   can determine out-of-order and dropped messages, if any.

To solve the serialization problem, we use [flatbuffers][4], which can be used
in an lock-free and allocation-free manner (Flatbuffers' object-based API is not
allowed). Careful manual management of the buffer space and manual copying of
memory may occasionally be needed to avoid accidentally overwriting or reusing
memory that you're not supposed to overwrite/reuse.

[4]: https://flatbuffers.dev/

To solve the kernel API problem, we use the POSIX socket API directly
(investigations into `io_uring` may occur at a later time) as opposed to use
wrapper libraries, as many libraries have internal allocations or locks that are
difficult to audit. Non-blocking API calls must be used so the socket API call
cannot block the rest of the real-time loop.

Since UDP is a fire-and-forget style protocol, we need a simple way for the
system to establish a connection, send heartbeat to ensure that they are still
present, and count the number of messages received thus far (and use that
information to reject out-of-order messages). This is all programmed manually
and integrated with the application real-time loop.

#### Session and message count handling

Since we assume a closed network without bad actors, we don't need a full
session that binds one client to one server. Instead, the client simply sends a
`HELLO` message and the server sends a `HELLO` response. This indicates to the
client that the server is up and can accept message. This is done during the
`.Connect` method of the client.

Since messages can be lost and/or reordered by UDP, we need to detect this. Each
message prepended with a message header that has an incrementing message ID. The
receive side can store the same counter and use it to detect missing/out of
order messages. Out of order messages are dropped.

### Kernel-side considerations

TBD.

TODOS
-----

- [ ] Implement session and message header functions
- [ ] Implement custom message header
- [ ] Implement data collection with loss logging, latency, etc.
- [ ] Figure out how to detect errors as errors are not transmitted synchronously.
- [ ] Figure out how to disallow data bigger than certain sizes from being transmitted in real time or at least do it in a way that makes sense...
- [ ] Figure out how to disable ARP and setup static mapping
- [ ] Figure out real-time priority of thread sending and receiving vs IRQ priority
- [ ] Figure out kernel configurations


Resources and links
-------------------

- https://arxiv.org/pdf/1808.10821.pdf
- https://ntrs.nasa.gov/api/citations/20200002393/downloads/20200002393.pdf
- https://github.com/google/flatbuffers/issues/5135
- https://flatbuffers.dev/flatbuffers_guide_use_cpp.html
  - Note access on untrusted data to validate buffer lengthllo.
