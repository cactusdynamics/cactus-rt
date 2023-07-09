add_executable(rt_signal_handling_example
  main.cc
)

target_link_libraries(rt_signal_handling_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_signal_handling_example)
