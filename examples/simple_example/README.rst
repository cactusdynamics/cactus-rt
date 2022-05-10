==================
``simple_example``
==================

This example shows one of the simplest possible application with this
framework. All it has is a single ``CyclicFifoThread``, which loops by default
at 1 kHz. It can serve as a template for more advanced applications.

Additionally, this application also shows how to set CPU affinity. By default,
the code pins the RT thread on core 2 (remember core starts at 0 in Linux, but
1 on tools like ``htop``). To validate the CPU affinity, run this program and
then run:

.. code-block:: console

   $ sudo build/examples/simple_example/rt_simple_example &
   $ ps -T -eo pid,tid,cls,rtprio,psr,cmd  | grep rt_simple_example
   697469  697469  TS      -   2 sudo build/examples/simple_example/rt_simple_example
   697470  697470  TS      -   3 build/examples/simple_example/rt_simple_example
   697470  697471  FF     80   2 build/examples/simple_example/rt_simple_example
   697499  697499  TS      -   1 grep --color=auto rt_simple_example

The ``psr`` column shows the last scheduled processor of the process. Since an
application can have many threads with only one thread being scheduled with
FIFO/DEADLINE and an ``rtprio``, look for that thread in the output. In this
example, the 3rd row shows the RT thread and we can see it is on processor 2.

This also works with ``isolcpus`` turned on for core 2, and you can confirm
that yourself.
