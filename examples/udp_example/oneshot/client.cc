#include <simpleudp.h>

#include <iostream>

#include "robot_instantaneous_data_generated.h"

using cactus_rt::examples::udp_example::CreateRobotInstantaneousData;
using cactus_rt::examples::udp_example::Joint1D;
using cactus_rt::examples::udp_example::MotorData;
using cactus_rt::examples::udp_example::RobotState_Running;
using cactus_rt::simpleudp::Error;
using cactus_rt::simpleudp::SimpleUDP;

constexpr size_t kBufSize = 1024;

const char* ip = "127.0.0.1";
const char* port = "7838";

const char* defaultData = "hello world";

Joint1D ExampleJoint1D(double scale) {
  return Joint1D{
    1.1 * scale,
    2.4 * scale,
    3.0 * scale,
    0.5 * scale,
    0.5 * scale,
    0.5 * scale,
    0.5 * scale,
    12.45 * scale,
    -10.0 * scale};
}

MotorData ExampleMotorData(double scale) {
  return MotorData{
    1.0 * scale,
    25 * scale,
    1 * scale,
    true};
}

int main() {
  flatbuffers::FlatBufferBuilder builder(kBufSize);

  Joint1D j1 = ExampleJoint1D(1.0);
  Joint1D j2 = ExampleJoint1D(2.0);
  Joint1D j3 = ExampleJoint1D(3.0);

  MotorData m1 = ExampleMotorData(1.0);
  MotorData m2 = ExampleMotorData(2.0);
  MotorData m3 = ExampleMotorData(3.0);

  auto instantaneous_data = CreateRobotInstantaneousData(
    builder,
    RobotState_Running, &j1, &j2, &j3, &m1, &m2, &m3);

  builder.Finish(instantaneous_data);

  auto* buf = builder.GetBufferPointer();
  int   size = builder.GetSize();

  SimpleUDP client(ip, port);

  {
    auto err = client.Connect();
    if (err) {
      std::cerr << err->ToString() << "\n";
      return 1;
    }
  }

  {
    auto [bytes_sent, err] = client.Send(buf, size);
    if (err) {
      std::cerr << err->ToString() << "\n";
      return 1;
    }

    std::cout << "sent " << bytes_sent << " bytes to " << ip << ":" << port << "\n";
  }
}
