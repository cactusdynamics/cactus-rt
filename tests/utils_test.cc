#include "cactus_rt/utils.h"

#include <gtest/gtest.h>

TEST(UtilsTest, AddTimespecByNs) {
  struct timespec ts;
  ts.tv_sec = 100;
  ts.tv_nsec = 400'000'000;

  auto ts1 = cactus_rt::AddTimespecByNs(ts, 500'000'000);
  EXPECT_EQ(100, ts1.tv_sec);
  EXPECT_EQ(900'000'000, ts1.tv_nsec);

  ts1 = cactus_rt::AddTimespecByNs(ts, 600'000'000);
  EXPECT_EQ(101, ts1.tv_sec);
  EXPECT_EQ(0, ts1.tv_nsec);

  ts1 = cactus_rt::AddTimespecByNs(ts, 600'000'001);
  EXPECT_EQ(101, ts1.tv_sec);
  EXPECT_EQ(1, ts1.tv_nsec);

  ts1 = cactus_rt::AddTimespecByNs(ts, 1'700'000'000);
  EXPECT_EQ(102, ts1.tv_sec);
  EXPECT_EQ(100'000'000, ts1.tv_nsec);

  ts1 = cactus_rt::AddTimespecByNs(ts, -300'000'000);
  EXPECT_EQ(100, ts1.tv_sec);
  EXPECT_EQ(100'000'000, ts1.tv_nsec);

  ts1 = cactus_rt::AddTimespecByNs(ts, -400'000'001);
  EXPECT_EQ(99, ts1.tv_sec);
  EXPECT_EQ(999'999'999, ts1.tv_nsec);

  ts1 = cactus_rt::AddTimespecByNs(ts, -1'700'000'000);
  EXPECT_EQ(98, ts1.tv_sec);
  EXPECT_EQ(700'000'000, ts1.tv_nsec);
}
