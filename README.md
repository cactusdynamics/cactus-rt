Real time demo code
===================

This is a code demoing real time C++ on Linux. Specifically, I'm demonstrating
the use of pthreads to create RT threads (via `SCHED_FIFO`), memory locking,
a few data sharing techniques between RT and non-RT threads, and the use of
USDT.

Architecture
------------

There are three threads:

- `HighFrequencyController`: A "high-frequency" (1000Hz) RT thread that
  "controls" some output variable to be sent to hardware.
  - In the default configuration, nothing will be outputted.
- `LowFrequencyController`: A "low-frequency" (100Hz) RT thread that "controls"
  the `HighFrequencyController`.
- `DataMonitor`: A non-RT thread that logs the data coming from the RT threads
  and displays some statistics to the terminal.

Not everything is implemented yet

Data passing demos
------------------

| Done? | Source | Target | Name | Type | Mechanism | Description |
|-------|--------|--------|------|------|-----------|-------------|
| Partially | LF     | HF     | `flag` | `char` | `atomic` | A flag that controls enable/disable and the function to use |
| No | LF     | DM     | `flag` | `char` | FIFO | Same as above |
| No | LF     | HF     | `control_param` | `struct{int, float}` | CAS Loop | Some parameters |
| No | LF     | DM     | `control_param` | `struct{int, float}` | FIFO | Same as above |
| No | LF     | DM     | `control_param` | `struct{int, float}` | Double buffering | Same as above, but for displaying live in the terminal |
| Yes | HF     | DM     | `output` | `int` | `boost::spsc_queue` | The output data from the HF thread |

Dependencies
------------

On Debian 10:

```
$ sudo apt install sytemtap-sdt-dev libspdlog-dev libboost-all-dev python-pyparsing
```

Note that python-pyparsing is needed to get around a `NameError: global name
'ParseException' is not defined` in Debian buster.

BPF tracing
-----------

This introduces some significant latency in the code. Be aware.

This needs the most up-to-date bpftrace (0.14.1) and bcc (0.24.0). I had to
manually install these as no distro provides this out of the box.

Then, simply run `sudo tools/bpf/latency` before running the `rt_demo` binary.

Notes
-----

### Current mystery around better performance when system is loaded.

The current RT thread at commit ca9e74331433916776392e7a2d14bd120d16e9b5 has a
problem: when the system is stressed with `stress-ng -c 8` (on a 8vCPU system),
it the latency is better than when the system is idle. Now, this is performed
on a non RT kernel (`Linux w520 5.10.0-0.bpo.9-amd64 #1 SMP Debian
5.10.70-1~bpo10+1 (2021-10-10) x86_64 GNU/Linux`), but I don't understand why
this is the case yet (numbers are min, average, max in microseconds):

Without stress:

```
[2022-03-28 00:13:33.829] [debug] wakeup latency:    0.367      60.0301 98.654
[2022-03-28 00:13:33.829] [debug] iteration latency: 0.193      0.866515        1.61
```

With stress:

```
[2022-03-28 00:13:50.658] [debug] wakeup latency:    0.101      4.58501 40.064
[2022-03-28 00:13:50.658] [debug] iteration latency: 0.042      0.0773558       0.774
```
