#include <cactus_rt/experimental/lockless.h>
#include <cactus_rt/rt.h>

#include <chrono>
#include <iostream>

using cactus_rt::App;
using cactus_rt::CyclicThread;
using cactus_rt::Thread;
using cactus_rt::experimental::lockless::AtomicMessage;
using cactus_rt::experimental::lockless::spsc::RealtimeReadableValue;
using namespace std::chrono_literals;

struct Pose {
  // We want default constructed values to have a flag showing it is default
  // constructed. This is because the RealtimeReadableValue will default
  // construct a value and it can immediately be read. We need to tell the writer
  // it is invalid. It may not be necessary to do this in general.
  bool   valid = false;
  double x = 0.0;
  double y = 0.0;
  double z = 0.0;
  double roll = 0.0;
  double pitch = 0.0;
  double yaw = 0.0;

  Pose() = default;

  Pose(double xx, double yy, double zz, double ro, double pi, double ya) : valid(true),
                                                                           x(xx),
                                                                           y(yy),
                                                                           z(zz),
                                                                           roll(ro),
                                                                           pitch(pi),
                                                                           yaw(ya) {}
};

bool operator==(const Pose& p1, const Pose& p2) {
  return p1.x == p2.x &&
         p1.y == p2.y &&
         p1.z == p2.z &&
         p1.roll == p2.roll &&
         p1.pitch == p2.pitch &&
         p1.yaw == p2.yaw;
}

bool operator!=(const Pose& p1, const Pose& p2) {
  return !(p1 == p2);
}

/**
 * A struct that holds all the shared data so it can be passed to both the real-time and non-real-time threads
 */
struct Context {
  AtomicMessage<bool>         done = false;
  RealtimeReadableValue<Pose> target_pose = {};
};

/**
 * This is a real-time thread
 */
class RTThread : public CyclicThread {
  Context& ctx_;
  Pose     current_target_pose_;

  static cactus_rt::CyclicThreadConfig CreateThreadConfig() {
    cactus_rt::CyclicThreadConfig thread_config;
    thread_config.period_ns = 1'000'000;
    thread_config.cpu_affinity = std::vector<size_t>{2};
    thread_config.SetFifoScheduler(80);

    return thread_config;
  }

 public:
  RTThread(Context& ctx) : CyclicThread("RTThread", CreateThreadConfig()), ctx_(ctx) {}

 protected:
  bool Loop(int64_t /*now*/) noexcept final {
    if (ctx_.done.Read()) {
      return true;
    }

    const Pose new_pose = ctx_.target_pose.Read();
    if (!new_pose.valid) {
      return false;
    }

    if (new_pose != current_target_pose_) {
      current_target_pose_ = new_pose;
      LOG_INFO(
        Logger(),
        "detected new pose: {} {} {} {} {} {}",
        current_target_pose_.x,
        current_target_pose_.y,
        current_target_pose_.z,
        current_target_pose_.roll,
        current_target_pose_.pitch,
        current_target_pose_.yaw
      );
    }

    return false;
  }
};

class NonRTThread : public Thread {
  Context& ctx_;

  static cactus_rt::ThreadConfig CreateThreadConfig() {
    cactus_rt::ThreadConfig thread_config;
    thread_config.SetOtherScheduler();
    return thread_config;
  }

 public:
  NonRTThread(Context& ctx) : Thread("NonRTThread", CreateThreadConfig()), ctx_(ctx) {}

  void Run() final {
    ctx_.target_pose.Write(Pose(1.5, 2.5, 3.5, 4.5, 5.5, 6.5));
    std::this_thread::sleep_for(1s);

    // Realistically only one of these values should be visible on the real-time thread.
    ctx_.target_pose.Write(Pose(1.5, 2.5, 3.5, 4.5, 5.5, 7.5));
    ctx_.target_pose.Write(Pose(1.5, 2.5, 3.5, 4.5, 5.5, 8.5));
    std::this_thread::sleep_for(1s);

    ctx_.done.Write(true);
  }
};

int main() {
  Context ctx;
  auto    rt_thread = std::make_shared<RTThread>(ctx);
  auto    non_rt_thread = std::make_shared<NonRTThread>(ctx);

  App app;
  app.RegisterThread(rt_thread);
  app.RegisterThread(non_rt_thread);

  app.Start();
  app.Join();

  return 0;
}
