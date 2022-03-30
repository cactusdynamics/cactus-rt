#ifndef RT_DEMO_DATA_MONITOR_H_
#define RT_DEMO_DATA_MONITOR_H_

#include <boost/lockfree/spsc_queue.hpp>
#include <utility>
#include <vector>

#include "data_types.h"
#include "framework/thread.h"

using boost::lockfree::spsc_queue;

namespace rt_demo {
class DataMonitor : public framework::Thread {
  constexpr static int kQueueCapacity = 8 * 1024;

  // https://www.boost.org/doc/libs/1_56_0/doc/html/boost/lockfree/spsc_queue.html
  // When full: reject additional push with returning false. This might be OK.
  // When empty: will return nothing on pop. Really, we want the data monitor
  // to block here, tho.
  //
  // https://stackoverflow.com/questions/22486552/boostlockfreespsc-queue-busy-wait-strategy-is-there-a-blocking-pop
  //
  // TODO: could probably use a dynamically allocated capacity as it would be
  // constructed on initialization.
  spsc_queue<HFCOutput, boost::lockfree::capacity<kQueueCapacity>>
                                hf_fifo_;
  std::pair<uint64_t, uint64_t> hf_fifo_push_failed_;
  std::vector<HFCOutput>        hf_data_buf_;

  spsc_queue<LFCOutput, boost::lockfree::capacity<kQueueCapacity>>
                                lf_fifo_;
  std::pair<uint64_t, uint64_t> lf_fifo_push_failed_;
  std::vector<LFCOutput>        lf_data_buf_;

  double write_data_interval_;

 public:
  DataMonitor(double write_data_interval = 1.0) : Thread("DM", 0, SCHED_OTHER),
                                                  hf_fifo_push_failed_(0, 0),
                                                  lf_fifo_push_failed_(0, 0),
                                                  write_data_interval_(write_data_interval) {
    hf_data_buf_.reserve(kQueueCapacity);
    lf_data_buf_.reserve(kQueueCapacity);
  }

  /**
   * Logs the output data by pushing it into a FIFO.
   *
   * @returns true if the push operation is successful
   */
  bool LogOutput(const HFCOutput& data) noexcept;

 protected:
  virtual void Run() noexcept override final;

 private:
  void WriteData() noexcept;
};
}  // namespace rt_demo

#endif
