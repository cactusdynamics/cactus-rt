#include <simpleudp.h>

#include <chrono>
#include <iostream>
#include <thread>

#include "robot_instantaneous_data_generated.h"

using cactus_rt::examples::udp_example::GetRobotInstantaneousData;
using cactus_rt::examples::udp_example::RobotInstantaneousData;
using cactus_rt::simpleudp::Error;
using cactus_rt::simpleudp::SimpleUDP;

constexpr size_t kBufSize = 1024;
uint8_t          buf[kBufSize];

const char* ip = "0.0.0.0";
const char* port = "7838";

void PrintInstantaneousData(const RobotInstantaneousData* data) {
  const auto* j1 = data->j1();
  const auto* j2 = data->j2();
  const auto* j3 = data->j3();
  std::cout << "J1: P(" << j1->px() << "," << j1->py() << "," << j1->pz() << ")\n";
  std::cout << "J2: P(" << j2->px() << "," << j2->py() << "," << j2->pz() << ")\n";
  std::cout << "J3: P(" << j3->px() << "," << j3->py() << "," << j3->pz() << ")\n";

  const auto* m1 = data->m1();
  const auto* m2 = data->m2();
  const auto* m3 = data->m3();
  std::cout << "M1: omega=" << m1->omega() << ", temp=" << m1->temp() << ", current=" << m1->current() << "\n";
  std::cout << "M2: omega=" << m2->omega() << ", temp=" << m2->temp() << ", current=" << m2->current() << "\n";
  std::cout << "M3: omega=" << m3->omega() << ", temp=" << m3->temp() << ", current=" << m3->current() << "\n";
  std::cout << "\n";
}

int main() {
  using namespace std::chrono_literals;

  SimpleUDP server(ip, port);

  {
    auto err = server.Bind();
    if (err) {
      std::cerr << err->ToString() << "\n";
      return 1;
    }
  }

  {
    while (true) {
      auto [bytes_received, err] = server.Recv(buf, kBufSize);
      if (err) {
        if (err->IsEAgain()) {
          std::this_thread::sleep_for(2ms);
          continue;
        }
        std::cerr << err->ToString() << "\n";
        return 1;
      }

      const auto* instantaneous_data = GetRobotInstantaneousData(buf);
      PrintInstantaneousData(instantaneous_data);
    }
  }

  return 0;
}
