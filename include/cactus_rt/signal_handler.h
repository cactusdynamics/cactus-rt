#ifndef CACTUS_RT_SIGNAL_HANDLER_H_
#define CACTUS_RT_SIGNAL_HANDLER_H_

#include <semaphore.h>

#include <csignal>
#include <vector>

#include "app.h"

/// Namespace comment is needed for doxygen to generate cross references correctly.
namespace cactus_rt {
/**
 * @brief Sets up termination signal handlers which enables the calling of
 * App::OnTerminationSignal when used with
 * cactus_rt::WaitForAndHandleTerminationSignal. Without calling this method,
 * signals will not be caught.
 *
 * To use this, you must also use either
 * cactus_rt::WaitForAndHandleTerminationSignal(app) or
 * cactus_rt::HasTerminationSignalBeenReceived following App::Start. For example
 * (see [signal_handler_example](https://github.com/cactusdynamics/cactus-rt/tree/master/examples/signal_handling_example)
 * for more details):
 *
 *     class MyApp : public cactus_rt::App { ... };
 *     int main() {
 *       cactus_rt::SetUpTerminationSignalHandler();
 *
 *       cactus_rt::App app;
 *       app.RegisterThread(my_thread1);
 *       app.RegisterThread(my_thread2);
 *       app.Start();
 *
 *       cactus_rt::WaitForAndHandleTerminationSignal();
 *       // Do my cleanup
 *       return 0;
 *     }
 *
 * When a signal listed in `signals` is sent,
 * cactus_rt::WaitForAndHandleTerminationSignal is unblocked. Further calls to
 * cactus_rt::HasTerminationSignalBeenReceived will return true.
 *
 * @param signals A vector of signals to catch. Default: SIGINT and SIGTERM.
 */
void SetUpTerminationSignalHandler(std::vector<int> signals = {SIGINT, SIGTERM});

/**
 * @brief Wait until a termination signal as setup via
 * cactus_rt::SetUpTerminationSignalHandler is sent.
 *
 * Calling this function effectively causes the application to run indefinitely
 * until a signal (such as via CTRL+C or kill) is received.
 *
 * This function should only be called from the main function. If this function
 * is called from multiple threads, it may block one of the threads
 * indefinitely.
 *
 * If this function is never called after calling
 * cactus_rt::SetUpTerminationSignalHandler, the signal caught by this
 * application will be ignored, unless you use the
 * HasTerminationSignalBeenReceived instead.
 *
 * This function is implemented via a semaphore, which is an async-signal-safe
 * method as listed in signal-safety(7).
 */
void WaitForAndHandleTerminationSignal();

/**
 * @brief Check if termination signal as setup via
 * cactus_rt::SetUpTerminationSignalHandler has already been received.
 *
 * This function can be used as a non-blocking, polling alternative to
 * WaitforAndHandleTerminationSignal.
 *
 * @returns true if termination signal has been received. false otherwise.
 */
bool HasTerminationSignalBeenReceived();
}  // namespace cactus_rt

#endif
