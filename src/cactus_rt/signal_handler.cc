#include "cactus_rt/signal_handler.h"

#include <unistd.h>

#include <cstring>

namespace cactus_rt {
/// @private
sem_t signal_semaphore;

/// @private
void HandleSignal(int /*sig*/) {
  // From the man page (sem_post(3)), it says:
  //
  // > sem_post() is async-signal-safe: it may be safely called within a
  // > signal handler.
  //
  // This allows it to be used for signaling for an async signal handler. This
  // is also according to Programming with POSIX Threads by Butenhof in 1997,
  // section 6.6.6.
  //
  // However, the situation is more complex, see https://stackoverflow.com/questions/48584862/sem-post-signal-handlers-and-undefined-behavior.
  // That said, overall this should be a good pattern to use.
  const int ret = sem_post(&signal_semaphore);
  if (ret != 0) {
    // Suppress warn_unused_result. yay c++.
    std::ignore = write(STDERR_FILENO, "failed to post semaphore\n", 25);
    std::_Exit(EXIT_FAILURE);
  }
}

void SetUpTerminationSignalHandler(std::vector<int> signals) {
  const int ret = sem_init(&signal_semaphore, 0, 0);
  if (ret != 0) {
    throw std::runtime_error{std::string("cannot initialize semaphore: ") + std::strerror(errno)};
  }

  for (auto signal : signals) {
    auto sig_ret = std::signal(signal, HandleSignal);
    if (sig_ret == SIG_ERR) {
      throw std::runtime_error(std::string("failed to register signal handler: ") + std::strerror(errno));
    }
  }
}

void WaitForAndHandleTerminationSignal() {
  // This function is not a part of the real signal handler. The real signal
  // handler (HandleSignal) posts to the semaphore, which unblocks this
  // function. This function then calls app.OnTerminationSignal() to allow for
  // graceful shutdown. Since this function is not executed as a signal handler,
  // it can call any arbitrary function.
  while (sem_wait(&signal_semaphore) == -1) {
  }
}

}  // namespace cactus_rt
