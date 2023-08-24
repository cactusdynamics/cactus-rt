Tracing example without using `cactus_rt::App`
==============================================

This example shows you how to use the tracing facilities of `cactus_rt` without
hooking up your threads into `App`. This requires a bit more effort but it is
not too difficult.

One thing about this approach: the thread id of the threads will not be setup
correctly. This is expected as that integration setup by `cactus_rt` and more
tedious to setup with out it.
