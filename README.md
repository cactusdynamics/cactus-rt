Real time demo code
===================

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

Data passing demos
------------------

| Source | Target | Type | Mechanism | Description |
|--------|--------|------|-----------|-------------|
| LF     | HF     | `char` | `atomic` | A flag that controls enable/disable and the function to use |
| LF     | DM     | `char` | FIFO | Same as above |
| LF     | HF     | `struct{int, float}` | CAS Loop | Some parameters |
| LF     | DM     | `struct{int, float}` | FIFO | Same as above |
| LF     | DM     | `struct{int, float}` | Double buffering | Same as above, but for displaying live in the terminal |
| HF     | DM     | `int` | FIFO | The output data from the HF thread |

Dependencies
------------

On Debian 10:

```
$ sudo apt install sytemtap-sdt-dev libspdlog-dev libboost-all-dev python-pyparsing
```

Note that python-pyparsing is needed to get around a `NameError: global name
'ParseException' is not defined` in Debian buster.
