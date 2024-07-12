#include "cactus_rt/experimental/lockless/atomic_bitset.h"

#include <gtest/gtest.h>

using AtomicBitset8 = cactus_rt::experimental::lockless::AtomicBitset<uint8_t>;
using AtomicBitset64 = cactus_rt::experimental::lockless::AtomicBitset<uint64_t>;

TEST(AtomicBitsetTest, SetResetAndLoad) {
  AtomicBitset8 bitset8;

  for (size_t i = 0; i < 8; i++) {
    EXPECT_FALSE(bitset8.Test(i));
  }

  bitset8.Set(0);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 0);
  }

  bitset8.Set(2);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 0 || i == 2);
  }

  bitset8.Set(7);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 0 || i == 2 || i == 7);
  }

  bitset8.Reset(7);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8[i], i == 0 || i == 2);
  }

  bitset8.Reset(6);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 0 || i == 2);
  }

  bitset8.Reset(0);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 2);
  }
}

TEST(AtomicBitsetTest, SetRangeResetRangeAndTest) {
  AtomicBitset8 bitset8;

  bitset8.SetRange({1, 6});

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), (i == 1) || (i == 6));
  }

  bitset8.ResetRange({1, 2});

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 6);
  }

  bitset8.SetRange({2, 6});

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), (i == 2) || (i == 6));
  }

  bitset8.ResetRange({1, 2, 6});

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), false);
  }
}

TEST(AtomicBitsetTest, FlipAndTest) {
  AtomicBitset8 bitset8;

  bitset8.Flip(2);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 2);
  }

  bitset8.FlipRange({2, 3, 7});

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8[i], (i == 3) || (i == 7));
  }

  bitset8.Flip(2);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8[i], (i == 2) || (i == 3) || (i == 7));
  }
}

TEST(AtomicBitsetTest, SetValueAndTest) {
  AtomicBitset8 bitset8;

  bitset8.SetValue(2, true);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8.Test(i), i == 2);
  }

  bitset8.SetValue(2, false);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8[i], false);
  }

  bitset8.SetValue(2, false);

  for (size_t i = 0; i < 8; i++) {
    EXPECT_EQ(bitset8[i], false);
  }
}

TEST(AtomicBitsetTest, OutOfRange) {
  AtomicBitset8 bitset8;
  EXPECT_DEATH(bitset8.Set(8), "");

  AtomicBitset64 bitset64;
  bitset64.Set(8);

  for (size_t i = 0; i < 64; i++) {
    EXPECT_EQ(bitset64[i], i == 8);
  }

  EXPECT_DEATH(bitset8.Set(64), "");
}
