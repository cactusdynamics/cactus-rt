add_executable(rt_message_passing_example
  main.cc
  data_logger_thread.cc
  rt_thread.cc
)

target_link_libraries(rt_message_passing_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_message_passing_example)

