#ifndef CACTUS_RT_LINUX_SCHED_EXT_H_
#define CACTUS_RT_LINUX_SCHED_EXT_H_

#include <sys/syscall.h>
#include <unistd.h>

#include <cstdint>

struct sched_attr {
  uint32_t size;

  uint32_t sched_policy;
  uint64_t sched_flags;

  /* SCHED_NORMAL, SCHED_BATCH */
  int32_t sched_nice;

  /* SCHED_FIFO, SCHED_RR */
  uint32_t sched_priority;

  /* SCHED_DEADLINE (nsec) */
  uint64_t sched_runtime;
  uint64_t sched_deadline;
  uint64_t sched_period;
};

inline long sched_setattr(pid_t pid, const struct sched_attr *attr, unsigned int flags) {
  return syscall(SYS_sched_setattr, pid, attr, flags);
}

inline long sched_getattr(pid_t pid, struct sched_attr *attr, unsigned int size, unsigned int flags) {
  return syscall(SYS_sched_getattr, pid, attr, size, flags);
}

#endif
