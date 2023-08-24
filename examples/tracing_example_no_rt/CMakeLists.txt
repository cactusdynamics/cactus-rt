add_executable(tracing_example_no_rt
  main.cc
)

target_link_libraries(tracing_example_no_rt
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(tracing_example_no_rt)

