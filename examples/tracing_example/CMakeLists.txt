add_executable(rt_tracing_example
  main.cc
)

target_link_libraries(rt_tracing_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_tracing_example)
