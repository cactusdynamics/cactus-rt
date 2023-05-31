#include "simpleudp.h"

#include <fcntl.h>
#include <unistd.h>

#include <cerrno>
#include <cstring>
#include <sstream>

namespace cactus_rt::simpleudp {

constexpr const char* kHello = "HELLO";
constexpr int         kHelloLength = 5;

std::string Error::ToString() const {
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

bool Error::IsEAgain() const {
  return errnum == EAGAIN || errnum == EWOULDBLOCK;
}

SimpleUDP::SimpleUDP(const char*               ip,
                     const char*               port,
                     std::chrono::milliseconds connectTimeout) : ip_(ip),
                                                                 port_(port),
                                                                 connectTimeout_(connectTimeout) {}

SimpleUDP::~SimpleUDP() {
  if (servinfo_ != nullptr) {
    freeaddrinfo(servinfo_);
  }

  if (fd_ != -1) {
    close(fd_);
  }
}

std::optional<Error> SimpleUDP::CreateSocket() {
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

std::optional<Error> SimpleUDP::Bind() {
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

std::optional<Error> SimpleUDP::Connect() {
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

  while (std::chrono::steady_clock::now() - start < connectTimeout_) {
    constexpr int bufLength = 16;
    char          buf[bufLength];
    auto [bytes_received, err] = Recv(buf, bufLength);
    if (err) {
      if (!err->IsEAgain()) {
        return err;
      } else {
        // TODO: sleep? pause?
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

std::pair<ssize_t, std::optional<Error>> SimpleUDP::Recv(void* buf, size_t len) const {
  ssize_t bytes_received = recv(fd_, buf, len, 0);
  if (bytes_received == -1) {
    return std::make_pair(0, Error{"recv", -1, errno, nullptr});
  }

  if (bytes_received == kHelloLength && strncmp(static_cast<char*>(buf), kHello, kHelloLength) == 0) {
    // Respond with a hello to notify client the server is ready to go.

    // TODO: send back to the IP address that we just received from...
    auto [_, err] = Send(kHello, kHelloLength);
    if (err) {
      // We don't want to retry (even though this is non-blocking socket) to not
      // double send HELLO. If something bad happens in the handshake, the
      // client should recreate the socket completely.
      return std::make_pair(0, err);
    }

    // Pretend we didn't get a message
    return std::make_pair(0, Error{"recv", -1, EAGAIN, nullptr});
  }

  return std::make_pair(bytes_received, std::nullopt);
}

std::pair<ssize_t, std::optional<Error>> SimpleUDP::Send(const void* buf, size_t len) const {
  ssize_t bytes_sent = send(fd_, buf, len, 0);
  if (bytes_sent == -1) {
    return std::make_pair(0, Error{"send", -1, errno, nullptr});
  }

  return std::make_pair(bytes_sent, std::nullopt);
}

}  // namespace cactus_rt::simpleudp
