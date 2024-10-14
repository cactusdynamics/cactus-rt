#include <cactus_rt/experimental/random.h>

#include <array>
#include <iomanip>
#include <iostream>
#include <random>

template <size_t N>
class Histogram {
  std::array<size_t, N> hist_;

 public:
  Histogram() : hist_({0}) {}

  void Record(float value) {
    const auto i = static_cast<size_t>(value * N);
    hist_.at(i)++;
  }

  void Display() {
    constexpr float width = 1.0F / static_cast<float>(N);
    float           current_bucket = 0.0F;
    for (size_t i = 0; i < N; i++) {
      std::cout << std::setprecision(4) << current_bucket << ": " << hist_[i] << "\n";
      current_bucket += width;
    }
  }
};

int main() {
  // Generate the seed once in non-real-time code.
  const uint64_t seed = std::random_device{}();
  std::cout << "Seed: " << seed << "\n";

  Histogram<20> hist;

  // Initialize the RNG state in non-real-time code.
  cactus_rt::experimental::random::Xorshift64Rand rng(seed);

  for (int i = 0; i < 1'000'000; i++) {
    // RealNumber(rng) is always O(1).
    const float num = cactus_rt::experimental::random::RealNumber(rng);
    if (num >= 1.0F || num < 0.0F) {
      std::cerr << "ERROR: seed = " << seed << " i = " << i << " num = " << num << " is out of range \n";
      return 1;
    }
    hist.Record(num);
  }
  hist.Display();
  return 0;
}
