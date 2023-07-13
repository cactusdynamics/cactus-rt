find_package(Protobuf REQUIRED)

# Need a separate directory for the protos because the generated files will be
# put into ${CMAKE_CURRENT_BINARY_DIR}. For this directory it will be in
# cactus_tracing/protos, which gives it a bit more sanity...
protobuf_generate_cpp(
  PROTO_GENERATED_SRCS
  PROTO_GENERATED_HEADERS
  trace.proto
  trace_packet.proto
  track_descriptor.proto
  thread_descriptor.proto
  process_descriptor.proto
  counter_descriptor.proto
  track_event.proto
  source_location.proto
)

# Having a static library will reduce compilation time and also allow the
# include directories and link libraries to be passed.
add_library(cactus_tracing_embedded_perfetto_protos
  STATIC
  ${PROTO_GENERATED_SRCS}
  ${PROTO_GENERATED_HEADERS}
)

target_link_libraries(cactus_tracing_embedded_perfetto_protos
  PUBLIC
  ${Protobuf_LIBRARIES}
)

target_include_directories(cactus_tracing_embedded_perfetto_protos
  SYSTEM PUBLIC # SYSTEM needed to suppress clang-tidy errors
  ${CMAKE_CURRENT_BINARY_DIR}
)
