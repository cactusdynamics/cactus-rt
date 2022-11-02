Include(FetchContent)

set(FETCHCONTENT_QUIET FALSE)

FetchContent_Declare(
  iceoryx
  GIT_REPOSITORY https://github.com/eclipse-iceoryx/iceoryx.git
  GIT_TAG        v2.0.2
  SOURCE_SUBDIR  iceoryx_meta
)

FetchContent_MakeAvailable(iceoryx)

# This is needed to make sure that when building the tests, catch2's headers
# are treated as system headers, as otherwise clang-tidy will run on them. This
# is different from the above because clang-tidy will run on the headers which
# is included from the tests, where as the above is for compiling catch2.
#
# After cmake 3.25, this shouldn't be needed anymore: https://gitlab.kitware.com/cmake/cmake/-/issues/18040
# get_target_property(CATCH2_INC Catch2 INTERFACE_INCLUDE_DIRECTORIES)
# set_target_properties(Catch2 PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CATCH2_INC}")
# set_target_properties(Catch2WithMain PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CATCH2_INC}")

add_executable(rt_iceoryx_example
  src/main.cc
)

target_include_directories(rt_iceoryx_example
  PRIVATE
  include
)

target_link_libraries(rt_iceoryx_example
  PRIVATE
  cactus_rt
  iceoryx_hoofs
  iceoryx_posh
)

if (ENABLE_CLANG_TIDY)
  set_target_properties(rt_iceoryx_example PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_iceoryx_example
  DESTINATION bin
)
