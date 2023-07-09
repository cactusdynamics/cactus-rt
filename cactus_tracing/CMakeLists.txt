# TODO: make this an independent project...
# cmake_minimum_required(VERSION 3.18)
# project(cactus_tracing)

find_package(Protobuf REQUIRED)

protobuf_generate_cpp(
  PROTO_GENERATED_SRCS
  PROTO_GENERATED_HEADERS
  protos/trace.proto
  protos/trace_packet.proto
  protos/track_descriptor.proto
  protos/thread_descriptor.proto
  protos/process_descriptor.proto
  protos/counter_descriptor.proto
  protos/track_event.proto
  protos/source_location.proto
)

add_library(cactus_tracing
  STATIC
  src/thread_tracer.cc
  ${PROTO_GENERATED_SRCS}
)

target_link_libraries(cactus_tracing
  PRIVATE
  ${Protobuf_LIBRARIES}
  ${PROTO_GENERATED_HEADERS}
)
