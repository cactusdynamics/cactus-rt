add_executable(rt_tracing_example
  main.cc
)

target_link_libraries(rt_tracing_example
  PRIVATE
  cactus_rt
)

if (ENABLE_CLANG_TIDY)
  set_target_properties(rt_tracing_example PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_tracing_example
  DESTINATION bin
)
