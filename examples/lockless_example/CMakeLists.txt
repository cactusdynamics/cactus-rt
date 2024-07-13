add_executable(rt_lockless_example
  main.cc
)

target_link_libraries(rt_lockless_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_lockless_example)
