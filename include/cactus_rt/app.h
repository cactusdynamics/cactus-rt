#ifndef CACTUS_RT_APP_H_
#define CACTUS_RT_APP_H_

#include <memory>
#include <optional>
#include <vector>

#include "quill/Quill.h"
#include "thread.h"
#include "tracing/tracer.h"

namespace cactus_rt {

/**
 * @brief A struct that serves as the configuration of App.
 */
struct AppConfig {
  const char*                  name = "RTApp";
  size_t                       reserved_heap_size = 0;
  std::optional<quill::Config> logger_config;

  std::vector<size_t> tracer_cpu_affinity_;
  std::vector<size_t> logger_background_thread_cpu_affinity_;  // TODO: this is unused
};

/**
 * @brief Creates a real-time application with multiple real-time and non-real-time threads.
 */
class App {
  const char* name_;

  // Size of heap to reserve in bytes at program startup.
  size_t heap_size_;

  // Configuration for quill logging
  quill::Config logger_config_;

  tracing::Tracer tracer_;

  std::vector<std::shared_ptr<BaseThread>> threads_;

  void SetDefaultLogFormat(quill::Config& cfg) {
    // Create a handler of stdout
    const std::shared_ptr<quill::Handler> handler = quill::stdout_handler();

    // Enable console colours on the handler
    static_cast<quill::ConsoleHandler*>(handler.get())->enable_console_colours();

    // Set the default pattern
    handler->set_pattern("[%(ascii_time)][%(level_id)][%(logger_name)][%(filename):%(lineno)] %(message)", "%Y-%m-%d %H:%M:%S.%Qns");
    cfg.default_handlers.push_back(handler);
  }

 public:
  explicit App(const AppConfig& config);

  virtual ~App() = default;

  // Copy constructors
  App(const App&) = delete;
  App& operator=(const App&) = delete;

  // Move constructors
  App(App&&) noexcept = default;
  App& operator=(App&&) noexcept = default;

  /**
   * @brief Registers a thread to be automatically started by the app. The start
   * order of the threads are in the order of registration.
   *
   * @param thread A shared ptr to a thread.
   */
  void RegisterThread(std::shared_ptr<BaseThread> thread);

  /**
   * @brief Starts the app by locking the memory and reserving the memory. Also
   * start all the threads in registration order.
   */
  virtual void Start();

  /**
   * @brief sends RequestStop to all threads in registration order.
   *
   * Provided for convenience only. If you want to stop in a different order,
   * you can override this method or implement your own functions.
   */
  virtual void RequestStop(bool stop_system_threads_only = false);

  /**
   * @brief Joins all the threads in registration order.
   *
   * Provided for convenience only. If you want to join in a different order,
   * you can override this method or implement your own functions.
   */
  virtual void Join(bool join_system_threads_only = false);

 protected:
  /**
   * Locks memory via mlockall and configure malloc to not give up memory nor
   * use mmap.
   */
  void LockMemory() const;

  /**
   * Reserve the heap based on the heap_size_.
   */
  void ReserveHeap() const;

  /**
   * Starts the Quill background logging thread.
   */
  void StartQuill();
};
}  // namespace cactus_rt

#endif
