include(FetchContent)

SET(FLATBUFFERS_BUILD_TESTS OFF)
SET(FLATBUFFERS_INSTALL OFF)

FetchContent_Declare(
  FlatBuffers
  GIT_REPOSITORY https://github.com/google/flatbuffers.git
  GIT_TAG        v23.5.26
  SYSTEM
)

FetchContent_MakeAvailable(FlatBuffers)

# simpleudp library as a starting point
add_library(cactus_rt_simpleudp
  STATIC
  simpleudp/simpleudp.cc
)

target_include_directories(cactus_rt_simpleudp
  PUBLIC
  simpleudp
)

target_compile_features(cactus_rt_simpleudp
  PUBLIC
  cxx_std_20
)

add_subdirectory(messages)
add_subdirectory(oneshot)
add_subdirectory(rtloop)

add_subdirectory(flatudp)
add_subdirectory(clientserver)

if (ENABLE_CLANG_TIDY)
  set_target_properties(cactus_rt_simpleudp PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

