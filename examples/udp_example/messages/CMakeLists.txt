# flatbuffer compilation
# note build_flatbuffers doesn't quite work right, so we go simpler buy doing add_custom_command

SET(FLATBUFFERS_MESSAGES_INCLUDE_DIR
  ${CMAKE_BINARY_DIR}/examples/udp_example/flatbuffers-generated
  CACHE INTERNAL "" # Need to make this variable visible to any subdirectories added later
)

# Could refactor this into a different cmake function...
add_custom_command(
  OUTPUT ${FLATBUFFERS_MESSAGES_INCLUDE_DIR}/robot_instantaneous_data_generated.h
  DEPENDS
    ${CMAKE_SOURCE_DIR}/examples/udp_example/messages/robot_instantaneous_data.fbs
    flatc
  COMMAND flatc --cpp -o ${FLATBUFFERS_MESSAGES_INCLUDE_DIR} ${CMAKE_SOURCE_DIR}/examples/udp_example/messages/robot_instantaneous_data.fbs
)

add_custom_target(flatbuffers_message_headers
  DEPENDS
    ${FLATBUFFERS_MESSAGES_INCLUDE_DIR}/robot_instantaneous_data_generated.h
)
