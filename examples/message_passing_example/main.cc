#include <cactus_rt/rt.h>

#include "data_logger_thread.h"
#include "rt_thread.h"

using cactus_rt::App;

int main() {
  App app;

  auto data_logger = app.CreateThread<DataLogger>("build/data.csv");
  auto rt_thread = app.CreateThread<RtThread>(data_logger);

  app.Start();
  rt_thread->Join();           // This thread will terminate on its own.
  data_logger->RequestStop();  // Stop the data logger after
  data_logger->Join();         // Wait for it to quit and flush everything.

  return 0;
}
