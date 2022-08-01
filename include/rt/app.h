#ifndef RT_DEMO_RT_APP_H_
#define RT_DEMO_RT_APP_H_

#include <cstddef>
#include <cstdint>

namespace cactus_rt {
class App {
  size_t heap_size_;

  /**
   * The start time of the application from the monotonic clock in nanoseconds.
   */
  int64_t start_monotonic_time_ns_;

  /**
   * The start time of the application from the realtime clock in nanoseconds.
   * Do not ever use this for any real-time sensitive computations.
   */
  int64_t start_wall_time_ns_;

 public:
  /**
   * Creates an instance of the RT app.
   *
   * @param heap_size The heap size to reserve in bytes. Defaults to 512MB.
   */
  App(size_t heap_size = 512 * 1024 * 1024) : heap_size_(heap_size) {}
  virtual ~App() = default;

  // Copy constructors
  App(const App&) = delete;
  App& operator=(const App&) = delete;

  // Move constructors
  App(App&&) noexcept = default;
  App& operator=(App&&) noexcept = default;

  /**
   * Starts the app by locking the memory and reserving the memory.
   */
  virtual void Start();

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
}  // namespace rt

#endif
