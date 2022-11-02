add_executable(rt_simple_example
  main.cc
)

target_link_libraries(rt_simple_example
  PRIVATE
  cactus_rt
)

if (ENABLE_CLANG_TIDY)
  set_target_properties(rt_simple_example PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_simple_example
  DESTINATION bin
)
