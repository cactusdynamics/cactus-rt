- Perfetto Tracing SDK allows userspace applications to emit app-specific
  events and data to a Perfetto trace.
  - Specifically, you can either emit time slices (regions/spans), counters, or
    custom data types based on a strongly-typed schema (protobuf?). 
  - Time slices and counters are emitted via "Track Events".
  - Custom data source are traced via a lambda function call (executed inline,
    and can be called concurrently). The data source itself is a subclass of
    `perfetto::DataSource`. There's only a single instance of this class
    usually, and you can store state on that instance?
- Track events can have custom data associated to them.
  - The documentation says two debug annotation in one place, but also says an
    arbitrary number of debug annotations in the detailed place.
  - Also can emit a "track", a "timestamp", and use a lambda to set custom
    values?
    - Separate thread have separate tracks. Is this automatic?
    - Tracks can have parent tracks (thread tracks belongs to process tracks).
  - Can emit custom protobuf message, but the message type has to be in the
    perfetto repo perfetto has to be rebuilt... See
    https://github.com/google/perfetto/issues/11. Closed as of two weeks ago
    but where?
- Counters are traced via the `TRACE_COUNTER` macro.
  - Doesn't seem like it has a beginning or ending, but just at some point in
    time (or can specify a specific time).

