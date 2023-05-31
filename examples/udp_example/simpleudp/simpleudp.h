#ifndef CACTUS_RT_SIMPLEUDP_H_
#define CACTUS_RT_SIMPLEUDP_H_

#include <netdb.h>
#include <sys/socket.h>
#include <sys/types.h>

#include <chrono>
#include <optional>
#include <string>
#include <utility>

namespace cactus_rt::simpleudp {
/**
 * A simple error class that allows us to return errors without allocation or printing.
 * Note all strings are const char* and should be compile time constant strings.
 */
struct Error {
  /**
   * This is usually the name of the system call/function that was called.
   */
  const char* source;

  /**
   * This is usually the return code of the system call/function that was called.
   */
  int code;

  /**
   * This is the errno value at the time of the error.
   */
  int errnum;

  /**
   * Custom message, if any
   */
  const char* msg;

  /**
   * Converts the error into a string message.
   *
   * Not real-time safe as it constructs a string.
   */
  std::string ToString() const;

  /**
   * Check if the error means to poll again. Check if errno is EAGAIN or EWOULDBLOCK.
   */
  bool IsEAgain() const;
};

/**
 * A simple UDP wrapper for Linux that makes it slightly easier to write code
 * without having to dive into each system call.
 *
 * This is designed for real-time communications between one client and one
 * server over a dedicated ethernet link without any other traffic.
 */
class SimpleUDP {
 private:
  const char*               ip_;
  const char*               port_;
  std::chrono::milliseconds connectTimeout_;

  struct addrinfo* servinfo_ = nullptr;
  int              fd_ = -1;

 public:
  SimpleUDP(const char* ip, const char* port, std::chrono::milliseconds connectTimeout = std::chrono::milliseconds(500));
  ~SimpleUDP();

  // Non-copyable
  SimpleUDP(const SimpleUDP& other) = delete;
  SimpleUDP operator=(const SimpleUDP& other) = delete;

  // Non-movable
  SimpleUDP(SimpleUDP&& other) = delete;
  SimpleUDP operator=(SimpleUDP&& other) = delete;

  std::optional<Error> Bind();
  std::optional<Error> Connect();

  std::pair<ssize_t, std::optional<Error>> Recv(void* buf, size_t len) const;
  std::pair<ssize_t, std::optional<Error>> Send(const void* buf, size_t len) const;

 private:
  std::optional<Error> CreateSocket();
};

}  // namespace cactus_rt::simpleudp

#endif
