add_executable(random_example
  main.cc
)

target_link_libraries(random_example
  PRIVATE
  cactus_rt
)

setup_cactus_rt_target_options(random_example)

