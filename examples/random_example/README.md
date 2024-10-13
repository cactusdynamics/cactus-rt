`random_example`
================

Technically, [none of the random number generators in C++ are O(1)][1]. This
means there is a small (infinitesimal?) probability that it may cause real-time
problems (for some of the implementation it may be near impossible). To ensure
absolute safety at the cost of slightly non-uniform random number generation,
cactus-rt implements a O(1) random number generator with the Xorshift algorithm.
This example shows how to use it.

**WARNING: DO NOT USE THIS RNG IN SECURE CRYPTOGRAPHIC CONTEXT AS IT IS NOT PERFECTLY RANDOM**.

[1]: https://youtu.be/Tof5pRedskI?t=2514
