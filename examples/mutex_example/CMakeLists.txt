add_executable(rt_mutex_example
  main.cc
)

target_link_libraries(rt_mutex_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(rt_mutex_example)
