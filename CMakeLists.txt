cmake_minimum_required(VERSION 3.18)
project(cactus_rt)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(ENABLE_CLANG_TIDY "Run clang-tidy" OFF)
option(ENABLE_EXAMPLES "Build example programs" ON)
option(BUILD_DOCS "Build documentations" OFF)

# https://stackoverflow.com/questions/5395309/how-do-i-force-cmake-to-include-pthread-option-during-compilation
set(CMAKE_THREAD_PREFER_PTHREAD TRUE)
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)

add_library(cactus_rt
  STATIC
  src/app.cc
  src/thread.cc
  src/cyclic_thread.cc
  src/signal_handler.cc
)

target_include_directories(cactus_rt
  PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_link_libraries(cactus_rt
  PRIVATE
  Threads::Threads
)

if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  if (ENABLE_CLANG_TIDY)
    find_program(CLANG_TIDY clang-tidy clang-tidy-16 clang-tidy-15 clang-tidy-14 clang-tidy-13 clang-tidy-12 clang-tidy-11)
  else()
    message(STATUS "Not running clang-tidy. Use ENABLE_CLANG_TIDY=ON to run clang-tidy.")
  endif()
endif()

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
      set_target_properties(${target_name} PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
    endif()
  endif()
endfunction()

setup_cactus_rt_target_options(cactus_rt)

# Build tests, examples, docs, only if this project is not embedded in another
# project.
if(${CMAKE_PROJECT_NAME} STREQUAL ${PROJECT_NAME})
  include(CTest)

  if (BUILD_TESTING)
    add_subdirectory(tests)
  endif()

  if (ENABLE_EXAMPLES)
    message(STATUS "Building example programs. Turn it off via ENABLE_EXAMPLES=OFF")
    add_subdirectory(examples/simple_example)
    add_subdirectory(examples/simple_deadline_example)
    add_subdirectory(examples/signal_handling_example)
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
