# TODO: make this an independent project...
# cmake_minimum_required(VERSION 3.18)
# project(cactus_tracing)

add_subdirectory(protos)

add_library(cactus_tracing
  STATIC
  src/cactus_tracing/thread_tracer.cc
)

target_include_directories(cactus_tracing
  PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_link_libraries(cactus_tracing
  PRIVATE
  cactus_tracing_embedded_perfetto_protos
)

add_executable(cactus_tracing_direct_proto_serialization
  src/utils/direct_proto_serialization.cc
)

target_link_libraries(cactus_tracing_direct_proto_serialization
  PRIVATE
  cactus_tracing_embedded_perfetto_protos
)
