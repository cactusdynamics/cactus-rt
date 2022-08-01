Blog examples
=============

These are barebone examples **without** using the `rt` library. This serves as
complementary material to the blog post published at:
https://shuhaowu.com/blog/2022/04-linux-rt-appdev-part4.html

There are three examples:

- `basic.cpp` which shows a simple RT thread.
- `loop.cpp` which shows a simple RT thread that loops.
- `mutex.cpp` which shows the usage of the ``cactus_rt::mutex``.

For more complete and complex examples, see the `examples` directory of this
repo, which uses the `rt` library.

To run the examples:

```
$ make
$ sudo ./basic
$ sudo ./loop
$ ./mutex
```
