Signal handling example
=======================

Many real-time application runs indefinitely until a termination signal is sent
from the OS, at which it gracefully shuts down. This example shows you how to
setup something like this with the built-in signal handling system.

Hints:

- You can ignore the signals if you simply ignore calling
  `cactus_rt::WaitUntilTerminationSignal`. However, if still want to run the
  application indefinitely, you will need to ensure the main thread is alive
  yourself.