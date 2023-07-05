#ifndef CACTUS_RT_APP_H_
#define CACTUS_RT_APP_H_

#include <memory>
#include <vector>

#include "thread.h"

namespace cactus_rt {
class App {
  // Size of heap to reserve in bytes at program startup.
  size_t heap_size_;

  std::vector<std::shared_ptr<BaseThread>> threads_;

 public:
  explicit App(size_t heap_size = 0) : heap_size_(heap_size) {}
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
  virtual void RequestStop();

  /**
   * @brief Joins all the threads in registration order.
   *
   * Provided for convenience only. If you want to join in a different order,
   * you can override this method or implement your own functions.
   */
  virtual void Join();

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
};
}  // namespace cactus_rt

#endif
