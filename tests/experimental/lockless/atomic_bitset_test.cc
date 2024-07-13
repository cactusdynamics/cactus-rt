#include "cactus_rt/experimental/lockless/atomic_bitset.h"

#include <gtest/gtest.h>

using AtomicBitset32 = cactus_rt::experimental::lockless::AtomicBitset<uint32_t>;
using AtomicBitset64 = cactus_rt::experimental::lockless::AtomicBitset<uint64_t>;

TEST(AtomicBitsetTest, SetResetAndLoad) {
  AtomicBitset32 bitset32;

  for (size_t i = 0; i < 32; i++) {
    EXPECT_FALSE(bitset32.Test(i));
  }

  bitset32.Set(0);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 0);
  }

  bitset32.Set(2);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 0 || i == 2);
  }

  bitset32.Set(7);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 0 || i == 2 || i == 7);
  }

  bitset32.Reset(7);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32[i], i == 0 || i == 2);
  }

  bitset32.Reset(6);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 0 || i == 2);
  }

  bitset32.Reset(0);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 2);
  }
}

TEST(AtomicBitsetTest, SetRangeResetRangeAndTest) {
  AtomicBitset32 bitset32;

  bitset32.SetRange({1, 6});

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), (i == 1) || (i == 6));
  }

  bitset32.ResetRange({1, 2});

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 6);
  }

  bitset32.SetRange({2, 6});

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), (i == 2) || (i == 6));
  }

  bitset32.ResetRange({1, 2, 6});

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), false);
  }
}

TEST(AtomicBitsetTest, FlipAndTest) {
  AtomicBitset32 bitset32;

  bitset32.Flip(2);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 2);
  }

  bitset32.FlipRange({2, 3, 7});

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32[i], (i == 3) || (i == 7));
  }

  bitset32.Flip(2);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32[i], (i == 2) || (i == 3) || (i == 7));
  }
}

TEST(AtomicBitsetTest, SetValueAndTest) {
  AtomicBitset32 bitset32;

  bitset32.SetValue(2, true);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32.Test(i), i == 2);
  }

  bitset32.SetValue(2, false);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32[i], false);
  }

  bitset32.SetValue(2, false);

  for (size_t i = 0; i < 32; i++) {
    EXPECT_EQ(bitset32[i], false);
  }
}

TEST(AtomicBitsetTest, OutOfRange) {
#ifdef RELEASE_BUILD
  GTEST_SKIP();  // won't die in release build
#endif

  AtomicBitset32 bitset32;
  EXPECT_DEATH(bitset32.Set(32), "");

  AtomicBitset64 bitset64;
  bitset64.Set(8);

  for (size_t i = 0; i < 64; i++) {
    EXPECT_EQ(bitset64[i], i == 8);
  }

  EXPECT_DEATH(bitset32.Set(64), "");
}
