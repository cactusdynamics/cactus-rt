add_executable(rt_simple_example
  main.cc
)

target_link_libraries(rt_simple_example
  PRIVATE
  rt_app_lib
)

