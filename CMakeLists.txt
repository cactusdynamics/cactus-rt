cmake_minimum_required(VERSION 3.16)
project(cactus_rt)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(ENABLE_CLANG_TIDY "Run clang-tidy" OFF)
option(ENABLE_EXAMPLES "Build example programs" ON)
option(ENABLE_TRACING "Enable runtime tracing support" ON)
option(ENABLE_ROS2 "Enables ROS2 support" OFF)
option(BUILD_DOCS "Build documentations" OFF)

# Used for building cactus-rt when all dependencies are vendored
option(CACTUS_RT_ENABLE_FETCH_DEPENDENCIES "Fetch dependencies during build" ON)

# https://stackoverflow.com/questions/5395309/how-do-i-force-cmake-to-include-pthread-option-during-compilation
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)

#########################
# External dependencies #
#########################

if(CACTUS_RT_ENABLE_FETCH_DEPENDENCIES)
  Include(FetchContent)

  FetchContent_Declare(
    quill
    GIT_REPOSITORY https://github.com/odygrd/quill.git
    GIT_TAG        9a270d5d6f57a3ac19451292e3a9f370fcd744b1
    # GIT_TAG        v3.3.2
  )

  FetchContent_MakeAvailable(quill)

# This is needed to make sure that when building the tests, catch2's headers
# are treated as system headers, as otherwise clang-tidy will run on them. This
# is different from the above because clang-tidy will run on the headers which
# is included from the tests, where as the above is for compiling catch2.
#
# After cmake 3.25, this shouldn't be needed anymore: https://gitlab.kitware.com/cmake/cmake/-/issues/18040
  get_target_property(QUILL_INC quill INTERFACE_INCLUDE_DIRECTORIES)
  set_target_properties(quill PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${QUILL_INC}")

  FetchContent_Declare(
    readerwriterqueue
    GIT_REPOSITORY    https://github.com/cameron314/readerwriterqueue.git
    GIT_TAG           v1.0.6
  )

  FetchContent_MakeAvailable(readerwriterqueue)
  get_target_property(READERWRITERQUEUE_INC readerwriterqueue INTERFACE_INCLUDE_DIRECTORIES)
  set_target_properties(readerwriterqueue PROPERTIES INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${READERWRITERQUEUE_INC}")
endif()

##########################################################
# Helper function to setup all cactus-rt related targets #
##########################################################

function(setup_cactus_rt_target_options target_name)
  # https://github.com/cpp-best-practices/cppbestpractices/blob/b1629eb/02-Use_the_Tools_Available.md#gcc--clang
  target_compile_options(${target_name}
    PRIVATE
    -Wall
    -Wextra
    -Wshadow
    -Wnon-virtual-dtor
    -pedantic

    -Wold-style-cast
    -Wcast-align
    -Wunused
    -Woverloaded-virtual
    -Wpedantic
    -Wconversion
    -Wsign-conversion
    -Wmisleading-indentation
    -Wduplicated-cond
    -Wduplicated-branches
    -Wlogical-op
    -Wnull-dereference
    -Wuseless-cast
    -Wdouble-promotion
    -Wformat=2
    -Wimplicit-fallthrough
  )

  target_compile_features(${target_name}
    PRIVATE
    cxx_std_17
  )

  if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
    if (ENABLE_CLANG_TIDY)
      # Need the extra args because g++ on 22.04 is by default C++17 which
      # means cmake won't generate the -std=gnu++17 flag, which causes
      # clang-tidy-14 (also 22.04 default) to fail.
      # Probably this issue: https://gitlab.kitware.com/cmake/cmake/-/issues/24238#note_1287978
      set_target_properties(${target_name} PROPERTIES CXX_CLANG_TIDY "${CLANG_TIDY};--extra-arg-before=-std=c++17")
    endif()
  endif()
endfunction()

#####################
# Cactus RT library #
#####################

if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  if (ENABLE_TRACING)
    add_subdirectory(protos)
  endif()
endif()

add_library(cactus_rt
  STATIC
  src/cactus_rt/app.cc
  src/cactus_rt/thread.cc
  src/cactus_rt/cyclic_thread.cc
  src/cactus_rt/signal_handler.cc
  src/cactus_rt/experimental/lockless/atomic_bitset.cc
)

target_include_directories(cactus_rt
  PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_link_libraries(cactus_rt
  PUBLIC
  quill::quill
  readerwriterqueue
  PRIVATE
  Threads::Threads
)

# Use a bounded queue
target_compile_definitions(cactus_rt PUBLIC QUILL_USE_BOUNDED_QUEUE)

if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  if (ENABLE_TRACING)
    target_sources(cactus_rt
      PRIVATE
      src/cactus_rt/tracing/sink.cc
      src/cactus_rt/tracing/thread_tracer.cc
      src/cactus_rt/tracing/trace_aggregator.cc
      src/cactus_rt/tracing/tracing_enabled.cc
      src/cactus_rt/tracing/utils/string_interner.cc
    )

    target_link_libraries(cactus_rt
      PUBLIC
      cactus_tracing_embedded_perfetto_protos
    )

    target_compile_definitions(cactus_rt
      PUBLIC
      CACTUS_RT_TRACING_ENABLED=1
    )
  endif()

  if (ENABLE_CLANG_TIDY)
    find_program(CLANG_TIDY clang-tidy clang-tidy-18 clang-tidy-17 clang-tidy-16 clang-tidy-15 clang-tidy-14)
  else()
    message(STATUS "Not running clang-tidy. Use ENABLE_CLANG_TIDY=ON to run clang-tidy.")
  endif()
endif()

setup_cactus_rt_target_options(cactus_rt)

# ROS 2 build support
if (ENABLE_ROS2)
  include(cmake/ros2.cmake)
endif()

# Build tests, examples, docs, only if this project is not embedded in another
# project.
if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  include(CTest)

  if (BUILD_TESTING)
    add_subdirectory(tests)
  endif()

  if (ENABLE_EXAMPLES)
    message(STATUS "Building example programs. Turn it off via ENABLE_EXAMPLES=OFF")
    add_subdirectory(examples/lockless_example)
    add_subdirectory(examples/logging_example)
    add_subdirectory(examples/message_passing_example)
    add_subdirectory(examples/mutex_example)
    add_subdirectory(examples/signal_handling_example)
    add_subdirectory(examples/simple_deadline_example)
    add_subdirectory(examples/simple_example)

    if (ENABLE_TRACING)
      add_subdirectory(examples/tracing_protos_example)
      add_subdirectory(examples/tracing_example)
      add_subdirectory(examples/tracing_example_no_rt)
    endif()
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
