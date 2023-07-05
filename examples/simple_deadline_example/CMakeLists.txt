add_executable(rt_simple_deadline_example
  main.cc
)

target_link_libraries(rt_simple_deadline_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_simple_deadline_example)
