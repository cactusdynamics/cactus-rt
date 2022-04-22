#include <limits.h>
#include <malloc.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/resource.h>  // needed for getrusage
#include <sys/resource.h>
#include <sys/time.h>  // needed for getrusage
#include <unistd.h>

#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string>

#ifndef LOCK_MEMORY
#define LOCK_MEMORY 1
#endif

// See also: https://rt.wiki.kernel.org/index.php/Verifying_mlockall()_effects_on_stack_memory_proof

constexpr static size_t kStackSize = 8 * 1024 * 1024;  // 8MB

pthread_t thread;
uint64_t  total = 0;

struct rusage start;
struct rusage end;

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

void PrefaultStack() {
  unsigned char buf[kStackSize];
  // This might be optimized out..., not sure.
  for (size_t i = 0; i < kStackSize; ++i) {
    buf[i] = i % 5 + 2;
    total += buf[i];
  }

  // This also can optimized out https://stackoverflow.com/questions/15538366/can-memset-function-call-be-removed-by-compiler
  // I see a lot of other people doing this.
  memset(buf, 2, kStackSize);
}

void* RunThread(void*) {
  getrusage(RUSAGE_THREAD, &start);

  PrefaultStack();

  getrusage(RUSAGE_THREAD, &end);
  return NULL;
}

void CreateThread() {
  pthread_attr_t attr;

  // Initialize the pthread attribute
  int ret = pthread_attr_init(&attr);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_init: " + std::to_string(ret));
  }

  // Set a stack size
  ret = pthread_attr_setstacksize(&attr, PTHREAD_STACK_MIN + kStackSize);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setstacksize: " + std::to_string(ret));
  }

  // Set the scheduler policy
  ret = pthread_attr_setschedpolicy(&attr, SCHED_FIFO);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setschedpolicy: " + std::to_string(ret));
  }

  // Set the scheduler priority
  struct sched_param param;
  param.sched_priority = 80;
  ret = pthread_attr_setschedparam(&attr, &param);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setschedparam: " + std::to_string(ret));
  }

  // Make sure threads created using the thread_attr_ takes the value from the attribute instead of inherit from the parent thread.
  ret = pthread_attr_setinheritsched(&attr, PTHREAD_EXPLICIT_SCHED);
  if (ret) {
    throw std::runtime_error("error in pthread_attr_setinheritsched: " + std::to_string(ret));
  }

  ret = pthread_create(&thread, &attr, RunThread, NULL);
  if (ret) {
    throw std::runtime_error("error in pthread_create: " + std::to_string(ret));
  }
}

int main() {
  if (LOCK_MEMORY) {
    LockMemory();
    std::cout << "Stack allocation with locked memory: \n";
  } else {
    std::cout << "Stack allocation without locked memory: \n";
  }

  CreateThread();
  pthread_join(thread, NULL);

  std::cout << "[Before] minor: " << start.ru_minflt << " | major: " << start.ru_majflt << "\n";
  std::cout << "[After]  minor: " << end.ru_minflt << " | major: " << end.ru_majflt << "\n";
  std::cout << "Ignore this value: " << total << "\n";

  return 0;
}
