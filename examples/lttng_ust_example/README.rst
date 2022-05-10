=====================
``lttng_ust_example``
=====================

This example demonstrates how to use `LTTNG-UST
<https://github.com/lttng/lttng-ust>`__ in a real-time application. LTTNG-UST
is an userspace tracing library that allows for very low overhead tracing (via
circular buffers and shared memory) that can be dynamically turned on and off.
Since the tracing is done entirely in userspace, it has significantly lower
overhead than `USDT
<https://leezhenghui.github.io/linux/2019/03/05/exploring-usdt-on-linux.html>`__,
which requires a kernel context switch.

Specifically, this example traces the start and end of the ``Loop`` function
with the wakeup and loop latency in microseconds. To run this code with tracer,
run from the top of the repo:

.. code-block:: console

   $ cmake --build build -j $(nproc)
   $ sudo examples/lttng_ust_example/trace.sh


This should run for 60 seconds and finally output something like

.. code::

   [OMITTED FOR BREVITY]

   [18:42:13.043671714] (+0.000965053) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 26.522 }
   [18:42:13.043675642] (+0.000003928) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.534 }
   [18:42:13.044701807] (+0.001026165) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 56.449 }
   [18:42:13.044705735] (+0.000003928) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.69 }
   [18:42:13.045704225] (+0.000998490) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 58.862 }
   [18:42:13.045708148] (+0.000003923) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.695 }
   [18:42:13.046702851] (+0.000994703) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 57.494 }
   [18:42:13.046706779] (+0.000003928) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.69 }
   [18:42:13.047671721] (+0.000964942) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 26.529 }
   [18:42:13.047675639] (+0.000003918) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.519 }
   [18:42:13.048696582] (+0.001020943) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 51.22 }
   [18:42:13.048700535] (+0.000003953) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.694 }
   [18:42:13.049703882] (+0.001003347) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 58.519 }
   [18:42:13.049707834] (+0.000003952) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.695 }
   [18:42:13.050702513] (+0.000994679) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 57.15 }
   [18:42:13.050706466] (+0.000003953) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.695 }
   [18:42:13.051672807] (+0.000966341) ubuntu rt_lttng_ust_example:loop_start: { cpu_id = 7 }, { wakeup_latency_us = 27.615 }
   [18:42:13.051676790] (+0.000003983) ubuntu rt_lttng_ust_example:loop_end: { cpu_id = 7 }, { loop_latency_us = 7.534 }

The trace output is also recorded into a file called ``trace.txt``

To-do:

* Show visualizing this data with trace compass.
