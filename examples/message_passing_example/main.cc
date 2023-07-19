#include <cactus_rt/rt.h>

#include "data_logger_thread.h"
#include "rt_thread.h"

using cactus_rt::App;
using cactus_rt::AppConfig;

int main() {
  AppConfig config;
  config.name = "message_passing_example";
  App app(config);

  auto data_logger = std::make_shared<DataLogger>("build/data.csv");
  auto rt_thread = std::make_shared<RtThread>(data_logger, 1'000'000);

  app.RegisterThread(data_logger);
  app.RegisterThread(rt_thread);

  app.Start();
  rt_thread->Join();           // This thread will terminate on its own.
  data_logger->RequestStop();  // Stop the data logger after
  data_logger->Join();         // Wait for it to quit and flush everything.

  return 0;
}
