CAS Exchange Loop
=================

This method is designed to pass data from a single non-RT producer to a single
RT consumer. The read on the consumer side (which is RT) is wait-free. The
write on the producer side waits if the RT side is using the value (without
waiting likely requires a queue?). This is almost like a lock, but only applies
to the non-RT side. To minimize non-RT side's waiting, you can copy the value
in the RT thread and immediately "release" the lock. Processing on the RT
thread with this cached value can occur afterwards. Changes to the read value
from the RT side is lost and is not passed back to the non-RT thread.

Originally invented in [farbot](https://github.com/hogliux/farbot) by Fabian
Renn-Giles and Dave Rowland. In their
[presentation](https://hogliux.github.io/farbot/presentations/meetingcpp_2019/assets/player/KeynoteDHTMLPlayer.html),
the algorithm is developed with three similar solutions, the first two of which
are flawed. All three algorithms are analyzed with TLA+.

V1: Memory leak
---------------

V2: ABA problem
---------------

V3: Working solution
--------------------
