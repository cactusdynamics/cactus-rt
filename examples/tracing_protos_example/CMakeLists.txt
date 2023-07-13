add_executable(tracing_synthetic_events
  synthetic_events.cc
)

target_link_libraries(tracing_synthetic_events
  PRIVATE
  cactus_tracing_embedded_perfetto_protos
)

setup_cactus_rt_target_options(tracing_synthetic_events)
