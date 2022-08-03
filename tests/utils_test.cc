#include "cactus_rt/utils.h"

#include <catch2/catch_test_macros.hpp>

TEST_CASE("Add timespec by nanoseconds", "[utils]") {
  struct timespec ts;
  ts.tv_sec = 100;
  ts.tv_nsec = 400'000'000;

  SECTION("by positive amounts") {
    auto ts1 = cactus_rt::AddTimespecByNs(ts, 500'000'000);
    REQUIRE(ts1.tv_sec == 100);
    REQUIRE(ts1.tv_nsec == 900'000'000);

    ts1 = cactus_rt::AddTimespecByNs(ts, 600'000'000);
    REQUIRE(ts1.tv_sec == 101);
    REQUIRE(ts1.tv_nsec == 0);

    ts1 = cactus_rt::AddTimespecByNs(ts, 600'000'001);
    REQUIRE(ts1.tv_sec == 101);
    REQUIRE(ts1.tv_nsec == 1);

    ts1 = cactus_rt::AddTimespecByNs(ts, 1'700'000'000);
    REQUIRE(ts1.tv_sec == 102);
    REQUIRE(ts1.tv_nsec == 100'000'000);
  }

  SECTION("by negative amounts") {
    auto ts1 = cactus_rt::AddTimespecByNs(ts, -300'000'000);
    REQUIRE(ts1.tv_sec == 100);
    REQUIRE(ts1.tv_nsec == 100'000'000);

    ts1 = cactus_rt::AddTimespecByNs(ts, -400'000'001);
    REQUIRE(ts1.tv_sec == 99);
    REQUIRE(ts1.tv_nsec == 999'999'999);

    ts1 = cactus_rt::AddTimespecByNs(ts, -1'700'000'000);
    REQUIRE(ts1.tv_sec == 98);
    REQUIRE(ts1.tv_nsec == 700'000'000);
  }
}
