#!/bin/bash

lttng create
lttng enable-event -u "rt_lttng_ust_example:*"
lttng start
build/examples/lttng_ust_example/rt_lttng_ust_example
lttng stop
lttng view | tee trace.txt
