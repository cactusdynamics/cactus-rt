#include <malloc.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <unistd.h>

#include <iostream>
#include <stdexcept>
#include <utility>

void LockMemory() {
  int ret;
  ret = mlockall(MCL_CURRENT | MCL_FUTURE);
  if (ret) {
    throw std::runtime_error{"mlockall failed: " + std::to_string(ret)};
  }

  ret = mallopt(M_TRIM_THRESHOLD, -1);
  if (ret == 0) {
    throw std::runtime_error{"mallopt M_TRIM_THRESHOLD failed"};
  }

  ret = mallopt(M_MMAP_MAX, 0);
  if (ret == 0) {
    throw std::runtime_error{"mallopt M_TRIM_THRESHOLD failed"};
  }
}

char *PrefaultHeap(int size, bool set_value) {
  char *buf;
  int   i;
  buf = static_cast<char *>(malloc(size));

  if (!buf) {
    perror("failed to malloc");
  }

  if (set_value) {
    for (i = 0; i < size; i += sysconf(_SC_PAGESIZE)) {
      buf[i] = 1;
    }
  }

  return buf;
}

std::pair<long, long> GetPageFaultCount() noexcept {
  std::pair<long, long> page_faults;

  struct rusage usage;
  getrusage(RUSAGE_THREAD, &usage);

  page_faults.first = usage.ru_minflt;
  page_faults.second = usage.ru_majflt;

  return page_faults;
}

int main() {
  LockMemory();

  constexpr size_t size = 1 * 1024 * 1024 * 1024;

  auto [minor1, major1] = GetPageFaultCount();

  char *buf1 = PrefaultHeap(size, true);

  auto [minor2, major2] = GetPageFaultCount();

  char *buf2 = PrefaultHeap(size, false);

  auto [minor3, major3] = GetPageFaultCount();

  for (int i = 0; i < size; i += sysconf(_SC_PAGESIZE)) {
    buf2[i] = 1;
  }

  auto [minor4, major4] = GetPageFaultCount();

  std::cout << "Page faults before:                   " << minor1 << ", " << major1 << "\n";
  std::cout << "Page faults after malloc + set value: " << minor2 << ", " << major2 << " | +" << (minor2 - minor1) << ", +" << (major2 - major1) << "\n";
  std::cout << "Page faults after malloc only:        " << minor3 << ", " << major3 << " | +" << (minor3 - minor2) << ", +" << (major3 - major2) << "\n";
  std::cout << "Page faults after set value:          " << minor4 << ", " << major4 << " | +" << (minor4 - minor3) << ", +" << (major4 - major3) << "\n";

  return 0;
}
