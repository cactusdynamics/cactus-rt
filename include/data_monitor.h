#ifndef RT_DEMO_DATA_MONITOR_H_
#define RT_DEMO_DATA_MONITOR_H_

#include <boost/lockfree/spsc_queue.hpp>
#include <utility>

#include "thread.h"

namespace rt_demo {
class DataMonitor : public Thread {
  // https://www.boost.org/doc/libs/1_56_0/doc/html/boost/lockfree/spsc_queue.html
  // When full: reject additional push with returning false.
  // When empty: will return nothing on pop.
  boost::lockfree::spsc_queue<std::pair<int64_t, int>, boost::lockfree::capacity<8 * 1024>> hf_output_fifo_;

  std::pair<uint64_t, uint64_t> hf_output_fifo_push_failed_;

 public:
  DataMonitor() : Thread(0, SCHED_OTHER),
                  hf_output_fifo_push_failed_(0, 0) {
  }

  /**
   * Logs the output data by pushing it into a FIFO.
   *
   * @param time The timestamp in nanoseconds
   * @returns true if the push operation is successful
   */
  bool LogOutput(int64_t time, int output);

 protected:
  virtual void Run() noexcept override final;
};
}  // namespace rt_demo

#endif
