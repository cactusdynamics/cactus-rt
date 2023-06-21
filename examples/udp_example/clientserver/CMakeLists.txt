# simple examples without cactus rt
add_executable(udp_flatbuffers_example_client
  client.cc
)

add_dependencies(udp_flatbuffers_example_client
  flatbuffers_message_headers
)

target_include_directories(udp_flatbuffers_example_client
  PRIVATE
  ${FLATBUFFERS_MESSAGES_INCLUDE_DIR}
)

target_link_libraries(udp_flatbuffers_example_client
  PRIVATE
  flatudp
  FlatBuffers::FlatBuffers
)

if (ENABLE_CLANG_TIDY)
  set_target_properties(udp_flatbuffers_example_client PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS udp_flatbuffers_example_client
  DESTINATION bin
)
