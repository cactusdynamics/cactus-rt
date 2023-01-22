cmake_minimum_required(VERSION 3.18)
project(cactus_rt)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(ENABLE_CLANG_TIDY "Run clang-tidy" OFF)
option(ENABLE_EXAMPLES "Build example programs" ON)
option(BUILD_DOCS "Build documentations" OFF)

# This is technically not right because build type could be a build-type
# variable due to multi-configuration generator. That said, ENABLE_TRACING is a
# configuration time variable so this is the right thing to do. It just means we
# can't easily build with ninja and visual studio, which is probably fine.
#
# See: https://mesos.apache.org/documentation/latest/cmake-examples/#building-debug-or-release-configurations
if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set(ENABLE_TRACING_DEFAULT ON)
else()
  set(ENABLE_TRACING_DEFAULT OFF)
endif()

option(ENABLE_TRACING
  "Build with Perfetto-based tracing enabled"
  ${ENABLE_TRACING_DEFAULT}
)

# https://stackoverflow.com/questions/5395309/how-do-i-force-cmake-to-include-pthread-option-during-compilation
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)
find_package(spdlog REQUIRED)

add_library(cactus_rt
  STATIC
  src/app.cc
  src/latency_tracker.cc
  src/signal_handler.cc
)

target_compile_features(cactus_rt
  PUBLIC
  cxx_std_20
)

target_include_directories(cactus_rt
  PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_link_libraries(cactus_rt
  PRIVATE
  Threads::Threads
  spdlog::spdlog
)

target_compile_options(cactus_rt
  PUBLIC # TODO: This should affect all the example programs as well, not sure if it this is a good idea tho
  -Wall
  -Wextra
  -Wpedantic
  -Wshadow
  -Wnon-virtual-dtor
  -Wpedantic
  -Wold-style-cast
  -Wcast-align
  -Wunused
  -Woverloaded-virtual
  -Wsign-conversion
  -Wmisleading-indentation
  -Wduplicated-cond
  -Wduplicated-branches
  -Wnull-dereference
  -Wuseless-cast
  -Wdouble-promotion
)

target_compile_definitions(cactus_rt
  PUBLIC
  "$<IF:$<CONFIG:Debug>,SPDLOG_ACTIVE_LEVEL=1,>"
)

if (ENABLE_TRACING)
  include(FetchContent)

  message(WARNING "Tracing with Perfetto is enabled as ENABLE_TRACING=${ENABLE_TRACING}. This is enabled by default in debug builds. However, this is not a real-time-safe configuration for production use and is for debug only!!! Change to a release build to ensure this is not turned on.")

  FetchContent_Declare(
    perfetto
    GIT_REPOSITORY https://android.googlesource.com/platform/external/perfetto
    GIT_TAG        v31.0 # Once v32 is released, change this v32.
    CONFIGURE_COMMAND ""
    BUILD_COMMAND     ""
  )

  FetchContent_MakeAvailable(perfetto)

  add_library(perfetto_sdk
    STATIC
    ${perfetto_SOURCE_DIR}/sdk/perfetto.cc
  )

  # TODO: should these be public?
  target_include_directories(cactus_rt
    SYSTEM PUBLIC
    ${perfetto_SOURCE_DIR}/sdk
  )

  target_link_libraries(cactus_rt
    PUBLIC
    perfetto_sdk
  )

  target_compile_definitions(cactus_rt
    PUBLIC
    ENABLE_TRACING=1
  )
endif()

# Only enable clang-tidy and ctest if this is the main project and not being included further.
if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  include(CTest)

  if (BUILD_TESTING)
    add_subdirectory(tests)
  endif()

  if (ENABLE_CLANG_TIDY)
    find_program(CLANG_TIDY clang-tidy clang-tidy-14 clang-tidy-13 clang-tidy-12 clang-tidy-11)
    set_target_properties(cactus_rt PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
  else()
    message(STATUS "Not running clang-tidy. Use ENABLE_CLANG_TIDY=ON to run clang-tidy.")
  endif()

  if (ENABLE_EXAMPLES)
    message(STATUS "Building example programs. Turn it off via ENABLE_EXAMPLES=OFF")
    add_subdirectory(examples/simple_example)
    add_subdirectory(examples/message_passing_example)
    add_subdirectory(examples/signal_handling_example)
    add_subdirectory(examples/mutex_example)
    add_subdirectory(examples/lttng_ust_example)
    add_subdirectory(examples/simple_deadline_example)
  endif()

  if (BUILD_DOCS)
    message(STATUS "Building documentations. Turn it off via BUILD_DOCS=OFF")
    find_package(Doxygen REQUIRED)

    set(DOXYGEN_FILE ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)
    configure_file(${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in ${DOXYGEN_FILE} @ONLY)

    add_custom_target(
      docs ALL
      COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_FILE}
      WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
      VERBATIM
    )
  endif()
endif()
