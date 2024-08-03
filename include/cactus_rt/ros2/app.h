#ifndef CACTUS_RT_ROS2_APP_H_
#define CACTUS_RT_ROS2_APP_H_
#include <memory>
#include <optional>
#include <type_traits>

#include "../app.h"
#include "ros2_adapter.h"

namespace cactus_rt::ros2 {

class Ros2ThreadMixin {
 protected:
  std::shared_ptr<Ros2Adapter> ros2_adapter_;

 public:
  void SetRos2Adapter(std::shared_ptr<Ros2Adapter> ros2_adapter) {
    ros2_adapter_ = ros2_adapter;
  }

  virtual void InitializeForRos2() = 0;
  virtual ~Ros2ThreadMixin() = 0;
};

class Ros2ExecutorThread : public cactus_rt::Thread, public cactus_rt::ros2::Ros2ThreadMixin {
  std::optional<rclcpp::executors::SingleThreadedExecutor> executor_;

  static cactus_rt::ThreadConfig CreateThreadConfig();

 public:
  Ros2ExecutorThread();

  void Run() override;

  void InitializeForRos2() override {}
};

class App : public cactus_rt::App {
  std::shared_ptr<Ros2Adapter>        ros2_adapter_;
  std::shared_ptr<Ros2ExecutorThread> ros2_executor_thread_;

 public:
  explicit App(
    std::string          name = "RTROS2App",
    cactus_rt::AppConfig config = cactus_rt::AppConfig(),
    Ros2Adapter::Config  ros2_adapter_config = Ros2Adapter::Config()
  );

  template <typename ThreadT, typename... Args>
  std::shared_ptr<ThreadT> CreateROS2EnabledThread(Args&&... args) {
    static_assert(std::is_base_of_v<Ros2ThreadMixin, ThreadT>, "Must derive ROS2 thread from Ros2ThreadMixin");
    std::shared_ptr<ThreadT> thread = std::make_shared<ThreadT>(std::forward<Args>(args)...);

    thread->SetRos2Adapter(ros2_adapter_);
    thread->InitializeForRos2();

    return thread;
  }

  void Start(int64_t start_monotonic_time_ns = -1) override;

  void RequestStop() override;

  void Join() override;
};

}  // namespace cactus_rt::ros2
#endif
