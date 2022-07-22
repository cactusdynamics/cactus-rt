#undef TRACEPOINT_PROVIDER
#define TRACEPOINT_PROVIDER rt_lttng_ust_example

#undef TRACEPOINT_INCLUDE
#define TRACEPOINT_INCLUDE "./tracepoint_provider.h"

#if !defined(_RT_LTTNG_UST_EXAMPLE_H_) || defined(TRACEPOINT_HEADER_MULTI_READ)
#define _RT_LTTNG_UST_EXAMPLE_H_

#include <lttng/tracepoint.h>

// NOLINTBEGIN

// Note the args is what's used by the application code.
// The fields are actually what's emitted in the ring buffer. The last argument
// in the field is the expression, using the "variable names" defined in the
// ARGS, that computes the value of that field.
//
// For example, you can emit an additional field with
// lttng_ust_field_float(double, wakeup_latency_us_2x, 2.0 * wakeup_latency_us)
//
// This would create another field called wakeup_latency_us_2x that is emitted.
// However, the computation of 2.0 * wakeup_latency_us is not done unless the
// tracepoint is enabled (?). This is done so more costly argument computations
// can be avoided when the tracepoint is disabled.
//
// See Example:lttng_ust_tracepoint() usage with a complex tracepoint definition.
// in https://lttng.org/docs/v2.13/#doc-probing-the-application-source-code
TRACEPOINT_EVENT(
  rt_lttng_ust_example,
  loop_start,
  TP_ARGS(
    double, wakeup_latency_us),
  TP_FIELDS(
    ctf_float(double, wakeup_latency_us, wakeup_latency_us)))

TRACEPOINT_EVENT(
  rt_lttng_ust_example,
  loop_end,
  TP_ARGS(
    double, loop_latency_us),
  TP_FIELDS(
    ctf_float(double, loop_latency_us, loop_latency_us)))

// NOLINTEND

#endif

#include <lttng/tracepoint-event.h>
