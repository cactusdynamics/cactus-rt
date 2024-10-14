#ifndef CACTUS_RT_EXPERIMENTAL_RAND_H_
#define CACTUS_RT_EXPERIMENTAL_RAND_H_

#include <cstdint>
#include <limits>

/**
 * C++'s random number engines and random number distributions are amortized
 * O(1) which as we know is greater than O(1) (theoretically O(inf)? But
 * statistically very unlikely?). See Real-time Programming with the C++
 * Standard Library - Timur Doumler - CppCon 2021[1].
 *
 * Thus we implement the Xorshift algorithm[2][3] to generate random numbers.
 * This is not a cryptographically safe random number generator. Notably the
 * uniform distribution implemented here do not guarantee perfect uniformity as
 * it never discard numbers to generate another number (to ensure we can
 * generate in O(1) and not amortized O(1)).
 *
 * [1]: https://youtu.be/Tof5pRedskI?t=2514
 * [2]: https://en.wikipedia.org/wiki/Xorshift
 * [3]: https://doi.org/10.18637/jss.v008.i14
 */

namespace cactus_rt::experimental::random {
class Xorshift64Rand {
  uint64_t x_;

 public:
  using result_type = uint64_t;

  // Xorshift cannot have an initial state of 0. So we set it to 4 as it was chosen by a random die.
  // (https://xkcd.com/221/)
  explicit Xorshift64Rand(result_type initial_state) : x_(initial_state == 0 ? 4 : initial_state) {
  }

  result_type operator()() {
    x_ ^= (x_ << 13);
    x_ ^= (x_ >> 7);
    x_ ^= (x_ << 17);
    return x_;
  };

  static constexpr result_type min() {
    return 1;
  }

  static constexpr result_type max() {
    return std::numeric_limits<uint64_t>::max();
  }
};

/**
 * @brief Return a random number between [0, 1). Similar to
 * std::uniform_real_distribution but not an object as it has no state. This is
 * not a perfect uniform distribution and has some minor amount of bias, which
 * is OK for real-time usage. It will also repeat as it doesn't allow you
 * reseed.
 *
 * @tparam T The data type of the return result, default to float.
 * @tparam Generator The random engine, default to Xorshift64Rand which is real-time safe.
 * @param rng The RNG generator instance.
 * @return T A random number between [0, 1)
 */
template <typename T = float, typename Generator = Xorshift64Rand>
T RealNumber(Generator& rng) {
  T v = static_cast<T>(rng() - Generator::min()) / static_cast<T>(Generator::max() - Generator::min());
  if (v == static_cast<T>(1.0)) {
    // Random numbers are supposed to be [0, 1). This is a hack to make sure we never land on 1.
    return static_cast<T>(0.0);
  }

  return v;
}

}  // namespace cactus_rt::experimental::random

#endif
