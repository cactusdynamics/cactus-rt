add_executable(rt_logging_example
  main.cc
)

target_link_libraries(rt_logging_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_logging_example)
