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
 * To use this, you must also use cactus_rt::WaitForAndHandleTerminationSignal(app)
 * following App::Start. For example (see
 * [signal_handler_example](https://github.com/cactusdynamics/cactus-rt/tree/master/examples/signal_handling_example)
 * for more details):
 *
 *     class MyApp : public cactus_rt::App { ... };
 *     int main() {
 *       cactus_rt::SetUpTerminationSignalHandler();
 *
 *       MyApp app;
 *       app.Start();
 *
 *       cactus_rt::WaitForAndHandleTerminationSignal(app);
 *       return 0;
 *     }
 *
 * When a signal listed in `signals` is sent,
 * cactus_rt::WaitForAndHandleTerminationSignal is unblocked and it calls
 * App::OnTerminationSignal. App::OnTerminationSignal is an user-defined method
 * on `MyApp` that should graceful shutdown the application.
 *
 * Readers familiar with signal handler safety (`man 7 signal-safety`) should
 * note that App::OnTerminationSignal is not a signal handler function, but
 * rather a function that can call any function without restrictions. This
 * should be obvious as it is called from
 * cactus_rt::WaitForAndHandleTerminationSignal on the main thread (in the above
 * case). This is implemented via a semaphore, which is an async-signal-safe
 * method as listed in `signal-safety(7)`.
 *
 * @param signals A vector of signals to catch. Default: SIGINT and SIGTERM.
 */
void SetUpTerminationSignalHandler(std::vector<int> signals = {SIGINT, SIGTERM});

/**
 * @brief Wait until a termination signal as setup via
 * cactus_rt::SetUpTerminationSignalHandler is sent, then runs
 * App::OnTerminationSignal. This function returns when
 * App::OnTerminationSignal returns.
 *
 * Calling this function effectively causes the application to run indefinitely
 * until a signal (such as via CTRL+C or kill) is received.
 *
 * This function should only be called from the main function. If this function
 * is called from multiple threads, it may block one of the threads
 * indefinitely.
 *
 * If this function is never called after calling cactus_rt::SetUpTerminationSignalHandler,
 * the signal caught by this application will be ignored.
 *
 * @param app The application object
 */
void WaitForAndHandleTerminationSignal(App& app);
}  // namespace cactus_rt

#endif
