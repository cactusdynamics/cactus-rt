add_executable(cactus_tracing_simple_example
  main.cc
)

target_link_libraries(cactus_tracing_simple_example
  PRIVATE
  cactus_tracing
)

setup_cactus_rt_target_options(cactus_tracing_simple_example)
