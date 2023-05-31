add_executable(rt_udp_client
  client.cc
)

add_dependencies(rt_udp_client
  flatbuffers_message_headers
)

target_include_directories(rt_udp_client
  PRIVATE
  ${FLATBUFFERS_MESSAGES_INCLUDE_DIR}
)

target_link_libraries(rt_udp_client
  PRIVATE
  cactus_rt
  cactus_rt_simpleudp
  FlatBuffers::FlatBuffers
)

add_executable(rt_udp_server
  server.cc
)

add_dependencies(rt_udp_server
  flatbuffers_message_headers
)

target_include_directories(rt_udp_client
  PRIVATE
  ${FLATBUFFERS_MESSAGES_INCLUDE_DIR}
)

target_link_libraries(rt_udp_server
  PRIVATE
  cactus_rt
  cactus_rt_simpleudp
  FlatBuffers::FlatBuffers
)

if (ENABLE_CLANG_TIDY)
  set_target_properties(rt_udp_server PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
  set_target_properties(rt_udp_client PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS rt_udp_server rt_udp_client
  DESTINATION bin
)

