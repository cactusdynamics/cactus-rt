Include(FetchContent)

FetchContent_Declare(
  perfetto
  GIT_REPOSITORY https://android.googlesource.com/platform/external/perfetto
  GIT_TAG        v29.0
  CONFIGURE_COMMAND ""
  BUILD_COMMAND ""
)

FetchContent_MakeAvailable(perfetto)

add_library(perfetto
  STATIC
  ${perfetto_SOURCE_DIR}/sdk/perfetto.cc
)

add_executable(rt_perfetto_example
  main.cc
)

target_include_directories(rt_perfetto_example
  SYSTEM # Want to disable clang-tidy on perfetto headers
  PRIVATE
  ${perfetto_SOURCE_DIR}/sdk
)

# TODO: does this need to link to thread given that cactus_rt already privately link to thread?
target_link_libraries(rt_perfetto_example
  PRIVATE
  cactus_rt
  perfetto
)

if (ENABLE_CLANG_TIDY)
  set_target_properties(rt_perfetto_example PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_perfetto_example
  DESTINATION bin
)
