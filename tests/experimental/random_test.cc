#include "cactus_rt/experimental/random.h"

#include <gtest/gtest.h>

#include <random>

using cactus_rt::experimental::random::RealNumber;
using cactus_rt::experimental::random::Xorshift64Rand;

TEST(RandomRealNumber, Generate) {
  const uint64_t seed = std::random_device{}();
  Xorshift64Rand rng(seed);

  for (int i = 0; i < 1'000'000; i++) {
    const float current = RealNumber(rng);
    if (current < 0.0F || current >= 1.0F) {
      ADD_FAILURE() << "number generated out of range: " << current << " (seed = " << seed << ", i = " << i << ")";
    }
  }

  for (int i = 0; i < 1'000'000; i++) {
    const auto current = RealNumber<double>(rng);
    if (current < 0.0 || current >= 1.0) {
      ADD_FAILURE() << "number generated out of range: " << current << " (seed = " << seed << ", i = " << i << ")";
    }
  }
}

TEST(RandomRealNumber, GenerateZeroSeed) {
  Xorshift64Rand rng(0);

  for (int i = 0; i < 1'000'000; i++) {
    const float current = RealNumber(rng);
    if (current < 0.0F || current >= 1.0F) {
      ADD_FAILURE() << "number generated out of range: " << current << " (seed = " << 0 << ", i = " << i << ")";
    }
  }

  for (int i = 0; i < 1'000'000; i++) {
    const auto current = RealNumber<double>(rng);
    if (current < 0.0 || current >= 1.0) {
      ADD_FAILURE() << "number generated out of range: " << current << " (seed = " << 0 << ", i = " << i << ")";
    }
  }
}

TEST(RandomRealNumber, DoesNotGenerate1) {
  struct MaxGenerator {
    using result_type = uint64_t;

    static constexpr result_type max() {
      return std::numeric_limits<uint64_t>::max();
    }

    static constexpr result_type min() {
      return 1;
    }

    result_type operator()() {
      return std::numeric_limits<uint64_t>::max();
    }
  };

  MaxGenerator rng;
  EXPECT_EQ(RealNumber(rng), 0.0F);
}
