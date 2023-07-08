`logging_example`
================

A simple example showing how to configure logging. Cactus RT uses [Quill](https://github.com/odygrd/quill) as a logger.

To configure logging, create your own `quill::Config` and pass it to the `App` constructor. Configuration options for Quill can be found in the [Quill documentation](https://quillcpp.readthedocs.io/en/latest/users-api.html#config-class). The log format can also be configured, as per the [formatting documetnation](https://quillcpp.readthedocs.io/en/latest/users-api.html#config-class).
