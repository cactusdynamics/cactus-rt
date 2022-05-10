#!/bin/bash

lttng create
lttng enable-event -u "rt_lttng_ust_example:*"
lttng start
sudo build/examples/lttng_ust_example/rt_lttng_ust_example

