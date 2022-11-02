Include(FetchContent)

set(FETCHCONTENT_QUIET FALSE)

FetchContent_Declare(
  Catch2
  GIT_REPOSITORY https://github.com/catchorg/Catch2.git
  GIT_TAG        v3.1.1
)

FetchContent_MakeAvailable(Catch2)

# This is needed to make sure that when building the tests, catch2's headers
# are treated as system headers, as otherwise clang-tidy will run on them. This
# is different from the above because clang-tidy will run on the headers which
# is included from the tests, where as the above is for compiling catch2.
#
# After cmake 3.25, this shouldn't be needed anymore: https://gitlab.kitware.com/cmake/cmake/-/issues/18040
get_target_property(CATCH2_INC Catch2 INTERFACE_INCLUDE_DIRECTORIES)
set_target_properties(Catch2 PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CATCH2_INC}")
set_target_properties(Catch2WithMain PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${CATCH2_INC}")

add_executable(cactus_rt_tests
  utils_test.cc
)

target_include_directories(cactus_rt_tests
  PRIVATE
  ${CMAKE_SOURCE_DIR}/include
)

target_link_libraries(cactus_rt_tests
  PRIVATE
  cactus_rt
  Catch2::Catch2WithMain
)

list(APPEND CMAKE_MODULE_PATH ${catch2_SOURCE_DIR}/extras)
include(CTest)
include(Catch)
catch_discover_tests(cactus_rt_tests)
