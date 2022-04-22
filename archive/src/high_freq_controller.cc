#include "high_freq_controller.h"

#include <spdlog/spdlog.h>

#include <cmath>
#include <iostream>

#include "utils/utils.h"

namespace rt_demo {
bool HighFrequencyController::Loop() noexcept {
  iterations_ += 1;

  int output = 0;
  if (!IsEnabled()) {
    return iterations_ >= max_iterations_;
  }

  auto    now_ts = Now();
  int64_t elapsed_ns = utils::TimespecDiffNanoseconds(now_ts, ref_time_);
  double  elapsed_ms = elapsed_ns / 1'000'000.0;

  double period = 1000;
  double threshold = 0.0;

  if (sin(2 * M_PI / period * elapsed_ms) >= threshold) {
    output = 1;
  } else {
    output = 0;
  }

  HFCOutput data{elapsed_ns, output};

  // TODO: check success?
  if (data_monitor_.LogOutput(data)) {
    ++data_logged_;
  }

  return iterations_ >= max_iterations_;
}

void HighFrequencyController::AfterRun() {
  CyclicRTThread::AfterRun();
  spdlog::debug("HFC logged data {} times", data_logged_);
}

void HighFrequencyController::SetEnabled(bool enabled) noexcept {
  char flag, new_flag;
  do {
    flag = flag_.load();
    new_flag = flag;
    if (enabled) {
      new_flag = flag | kFlagEnabledBit;
    } else {
      new_flag = flag & ~(kFlagEnabledBit);
    }
    // TODO: learn exactly the difference between weak and strong.
    // TODO: figure out if this while loop needs a timeout?
  } while (!flag_.compare_exchange_weak(flag, new_flag));
}

void HighFrequencyController::SetFunction(WaveFunction function) noexcept {
  // TODO: not implemented yet
}

bool HighFrequencyController::IsEnabled() const noexcept {
  return flag_.load() & kFlagEnabledBit;
}

HighFrequencyController::WaveFunction HighFrequencyController::CurrentFunction() const noexcept {
  return WaveFunction::SIN;
}
}  // namespace rt_demo
