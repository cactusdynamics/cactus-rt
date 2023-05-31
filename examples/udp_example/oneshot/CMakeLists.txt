# simple examples without cactus rt
add_executable(oneshot_udp_server
  server.cc
)

add_dependencies(oneshot_udp_server
  flatbuffers_message_headers
)

target_include_directories(oneshot_udp_server
  PRIVATE
  ${FLATBUFFERS_MESSAGES_INCLUDE_DIR}
)

target_link_libraries(oneshot_udp_server
  PRIVATE
  cactus_rt_simpleudp
  FlatBuffers::FlatBuffers
)

add_executable(oneshot_udp_client
  client.cc
)

target_include_directories(oneshot_udp_client
  PRIVATE
  ${FLATBUFFERS_MESSAGES_INCLUDE_DIR}
)

add_dependencies(oneshot_udp_client
  flatbuffers_message_headers
)

target_link_libraries(oneshot_udp_client
  PRIVATE
  cactus_rt_simpleudp
  FlatBuffers::FlatBuffers
)

if (ENABLE_CLANG_TIDY)
  set_target_properties(oneshot_udp_server PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
  set_target_properties(oneshot_udp_client PROPERTIES CXX_CLANG_TIDY ${CLANG_TIDY})
endif()

install(
  TARGETS oneshot_udp_server oneshot_udp_client
  DESTINATION bin
)
