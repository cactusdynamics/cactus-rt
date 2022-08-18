add_executable(rt_simple_example
  main.cc
)

target_link_libraries(rt_simple_example
  PRIVATE
  cactus_rt
)

install(
  TARGETS rt_simple_example
  DESTINATION bin
)
