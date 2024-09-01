add_executable(rt_lockless_realtime_read_example
  realtime_read.cc
)

target_link_libraries(rt_lockless_realtime_read_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_lockless_realtime_read_example)
