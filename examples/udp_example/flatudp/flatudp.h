#ifndef CACTUS_RT_FLATUDP_H_
#define CACTUS_RT_FLATUDP_H_

#include <fcntl.h>
#include <netdb.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <unistd.h>

#include <array>
#include <cerrno>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <optional>
#include <sstream>
#include <thread>
#include <utility>

namespace cactus_rt::flatudp {

constexpr const char* kHello = "HELLO";
constexpr int         kHelloLength = 5;

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
  std::string ToString() const {
    std::stringstream ss;

    constexpr size_t n = 128;

    char  buf[n];
    char* errstr = strerror_r(errnum, buf, n);  // must use the return value, not buf...

    ss << "simpleudp::Error(" << source << "): code=" << code << ", errno=" << errnum << " (" << errstr << ")";
    if (msg != nullptr) {
      ss << ", msg=" << msg;
    }

    return ss.str();
  }

  /**
   * Check if the error means to poll again. Check if errno is EAGAIN or EWOULDBLOCK.
   */
  bool IsEAgain() const {
    return errnum == EAGAIN || errnum == EWOULDBLOCK;
  }
};

template <typename T, int buf_size = 1024>
class FlatUDP {
  const char*               ip_;
  const char*               port_;
  std::chrono::milliseconds connect_timeout_;

  // TODO: maybe this can be dynamically allocated...
  std::array<uint8_t, buf_size> buf_;
  bool                          connection_established_ = false;
  uint64_t                      message_count_ = 0;

  struct addrinfo* servinfo_ = nullptr;
  int              fd_ = -1;

  FlatUDP(
    const char*               ip,
    const char*               port,
    std::chrono::milliseconds connect_timeout = std::chrono::milliseconds(500))
      : ip_(ip),
        port_(port),
        connect_timeout_(connect_timeout) {
  }

  ~FlatUDP() {
    if (servinfo_ != nullptr) {
      freeaddrinfo(servinfo_);
    }

    if (fd_ != -1) {
      close(fd_);
    }
  }

  // Non-copyable
  FlatUDP(const FlatUDP& other) = delete;
  FlatUDP operator=(const FlatUDP& other) = delete;

  // Non-movable
  FlatUDP(FlatUDP&& other) = delete;
  FlatUDP operator=(FlatUDP&& other) = delete;

 private:
  std::optional<Error> CreateSocket() {
    struct addrinfo hints;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_INET;  // Sorry, IPv4 only for this library...
    hints.ai_socktype = SOCK_DGRAM;

    int rc = getaddrinfo(ip_, port_, &hints, &servinfo_);
    if (rc != 0) {
      return Error{"getaddrinfo", rc, errno, nullptr};
    }

    if (servinfo_ == nullptr) {
      return Error{"getaddrinfo", rc, errno, "getaddrinfo got NULL addrinfo"};
    }

    fd_ = socket(servinfo_->ai_family, servinfo_->ai_socktype, servinfo_->ai_protocol);
    if (fd_ == -1) {
      return Error{"socket", fd_, errno, nullptr};
    }

    rc = fcntl(fd_, F_SETFL, O_NONBLOCK);
    if (rc == -1) {
      return Error{"fctnl", rc, errno, nullptr};
    }

    return std::nullopt;
  }

  std::pair<ssize_t, std::optional<Error>> SendBuf(void* buf, size_t len) const {
    ssize_t bytes_sent = send(fd_, buf, len, 0);
    if (bytes_sent == -1) {
      return std::make_pair(0, Error{"send", -1, errno, nullptr});
    }

    return std::make_pair(bytes_sent, std::nullopt);
  }

  std::pair<ssize_t, std::optional<Error>> RecvBuf(void* buf, size_t len) const {
    ssize_t bytes_received = recv(fd_, buf, len, 0);
    if (bytes_received == -1) {
      return std::make_pair(0, Error{"recv", -1, errno, nullptr});
    }

    if (!connection_established_ && bytes_received == kHelloLength && strncmp(static_cast<char*>(buf), kHello, kHelloLength) == 0) {
      // Respond with a hello to notify client the server is ready to go.

      // TODO: send back to the IP address that we just received from...
      auto [_, err] = SendBuf(kHello, kHelloLength);
      if (err) {
        // We don't want to retry (even though this is non-blocking socket) to not
        // double send HELLO. If something bad happens in the handshake, the
        // client should recreate the socket completely.
        return std::make_pair(0, err);
      }

      connection_established_ = true;

      // Pretend we didn't get a message
      return std::make_pair(0, Error{"recv", -1, EAGAIN, nullptr});
    }

    return std::make_pair(bytes_received, std::nullopt);
  }

 public:
  std::optional<Error> Bind() {
    std::optional<Error> err = CreateSocket();
    if (err) {
      return err;
    }

    int rc = bind(fd_, servinfo_->ai_addr, servinfo_->ai_addrlen);
    if (rc == -1) {
      close(fd_);
      return Error{"bind", rc, errno, nullptr};
    }

    return std::nullopt;
  }

  std::optional<Error> Connect() {
    std::optional<Error> err = CreateSocket();
    if (err) {
      return err;
    }

    if (connect(fd_, servinfo_->ai_addr, servinfo_->ai_addrlen) == -1) {
      return Error{"connect", -1, errno, nullptr};
    }

    {
      auto [_, err] = Send(kHello, kHelloLength);
      if (err) {
        return err;
      }
    }

    auto start = std::chrono::steady_clock::now();
    bool connected = false;

    while (std::chrono::steady_clock::now() - start < connect_timeout_) {
      constexpr int bufLength = 16;
      char          buf[bufLength];
      auto [bytes_received, err] = Recv(buf, bufLength);
      if (err) {
        if (!err->IsEAgain()) {
          return err;
        } else {
          // Sleep so we don't completely block the CPU as this thread is likely real-time.
          using namespace std::chrono_literals;
          std::this_thread::sleep_for(1ms);
        }
      } else {
        if (bytes_received == kHelloLength) {
          if (strncmp(buf, kHello, kHelloLength) == 0) {
            connected = true;
            break;
          }
        }
      }
    }

    if (!connected) {
      return Error{"handshake", -1, ECONNREFUSED, "cannot establish HELLO with remote host"};
    }

    return std::nullopt;
  }
};

}  // namespace cactus_rt::flatudp

#endif
