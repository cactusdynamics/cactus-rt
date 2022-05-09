================================
Real-time app framework and demo
================================

--------
Examples
--------

``simple_example``
------------------

``mutex_example``
-----------------

``message_passing_example``
---------------------------

------------
Dependencies
------------

Ubuntu/Debian
-------------

Tested on Debian 10 and Ubuntu 20.04:

```
$ sudo apt install libspdlog-dev liblttng-ust-dev
```

- `liblttng-ust-dev` is only used for the LTTng-UST testing.

----------
Validation
----------

Validating CPU affinity
-----------------------

.. code::

   ps -T -eo pid,tid,cls,rtprio,psr,cmd  | grep rt_simple_example

The ``psr`` column shows the last scheduled processor of the process. Since an
application can have many threads with only one thread being scheduled with
FIFO/DEADLINE and an ``rtprio``, look for that thread in the output.
