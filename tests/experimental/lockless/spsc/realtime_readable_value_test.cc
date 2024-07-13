#include "cactus_rt/experimental/lockless/spsc/realtime_readable_value.h"

#include <gtest/gtest.h>

struct Data {
  int    a = 1;
  double b = 2.0;
  float  c = 3.0F;
};

using RealtimeReadableData = cactus_rt::experimental::lockless::spsc::RealtimeReadableValue<Data>;

// A single threaded test only guarantees the very basic functionality.
// Multi-threaded tests is hard to achieve and guarantee any real outcome.
// We have TLA+ specification but it doesn't guarantee implementation correctness.
TEST(RealtimeReadableValueTest, ReadAndWrite) {
  RealtimeReadableData data;

  // Initial read
  auto data1 = data.Read();
  EXPECT_EQ(data1.a, 1);
  EXPECT_EQ(data1.b, 2.0);
  EXPECT_EQ(data1.c, 3.0F);

  // Initial write
  const Data new_data{2, 3.0, 4.0F};
  data.Write(new_data);

  // Read after write
  auto data2 = data.Read();
  EXPECT_EQ(data2.a, 2);
  EXPECT_EQ(data2.b, 3.0);
  EXPECT_EQ(data2.c, 4.0F);

  // Read again
  auto data3 = data.Read();
  EXPECT_EQ(data3.a, 2);
  EXPECT_EQ(data3.b, 3.0);
  EXPECT_EQ(data3.c, 4.0F);

  // Now write twice
  const Data new_data2{3, 4.0, 5.0F};
  data.Write(new_data2);

  const Data new_data3{4, 5.0, 6.0F};
  data.Write(new_data3);

  // Read again
  auto data4 = data.Read();
  EXPECT_EQ(data4.a, 4);
  EXPECT_EQ(data4.b, 5.0);
  EXPECT_EQ(data4.c, 6.0F);
}
