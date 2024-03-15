#include "cactus_rt/tracing/utils/string_interner.h"

#include <gtest/gtest.h>

#include <cstring>
#include <iostream>
#include <unordered_set>

using cactus_rt::tracing::utils::StringInterner;

namespace cactus_rt::tracing::utils {

TEST(StringInternerTest, BasicAssertions) {
  StringInterner interner;

  const char* const_char_arr = "hello";
  char        char_arr[sizeof(const_char_arr)];  // NOLINT(modernize-avoid-c-arrays,bugprone-sizeof-expression)
  strncpy(char_arr, const_char_arr, sizeof(char_arr));

  const std::string_view sv{const_char_arr};
  const std::string      str{const_char_arr};

  const auto [new1, id1] = interner.GetId("hello");
  const auto [new2, id2] = interner.GetId(const_char_arr);
  const auto [new3, id3] = interner.GetId(char_arr);
  const auto [new4, id4] = interner.GetId(sv);
  const auto [new5, id5] = interner.GetId(str);

  EXPECT_NE(const_char_arr, char_arr);  // Just a sanity check...

  // Everything should have the same id
  EXPECT_EQ(id1, id2);
  EXPECT_EQ(id1, id3);
  EXPECT_EQ(id1, id4);
  EXPECT_EQ(id1, id5);

  // Only one of them should be inserting.
  EXPECT_TRUE(new1);
  EXPECT_FALSE(new2);
  EXPECT_FALSE(new3);
  EXPECT_FALSE(new4);
  EXPECT_FALSE(new5);

  // We expect the size of the strings memoized to be 1.
  EXPECT_EQ(interner.Size(), 1);
}

TEST(StringInternerTest, ManyStrings) {
  StringInterner interner;

  const auto [new1, id1] = interner.GetId("hello1");
  const auto [new2, id2] = interner.GetId("hello2");
  const auto [new3, id3] = interner.GetId("hello3");
  const auto [new4, id4] = interner.GetId("hello4");
  const auto [new5, id5] = interner.GetId("hello5");
  const auto [new6, id6] = interner.GetId("hello6");
  const auto [new7, id7] = interner.GetId("hello7");
  const auto [new8, id8] = interner.GetId("hello8");
  const auto [new9, id9] = interner.GetId("hello9");

  const std::unordered_set<uint64_t> s{id1, id2, id3, id4, id5, id6, id7, id8, id9};

  EXPECT_EQ(s.size(), 9);
  EXPECT_EQ(interner.Size(), 9);

  for (const auto id : s) {
    EXPECT_NE(id, 0);
  }

  EXPECT_TRUE(new1);
  EXPECT_TRUE(new2);
  EXPECT_TRUE(new3);
  EXPECT_TRUE(new4);
  EXPECT_TRUE(new5);
  EXPECT_TRUE(new6);
  EXPECT_TRUE(new7);
  EXPECT_TRUE(new8);
  EXPECT_TRUE(new9);

  const std::string str{"hello1"};
  const auto [new10, id10] = interner.GetId(str.data());
  EXPECT_EQ(id1, id10);
  EXPECT_FALSE(new10);
  EXPECT_EQ(interner.Size(), 9);
}

TEST(StringInternerTest, OutOfScope) {
  StringInterner interner;

  uint64_t id1 = 0;
  bool     new1 = false;
  uint64_t id2 = 0;
  bool     new2 = true;  // intentionally wrong answer to ensure the expect is working

  {
    std::string s{"hello1"};
    const auto [n, i] = interner.GetId(s.data());
    new1 = n;
    id1 = i;
    s.replace(1, 1, "g");
  }

  {
    char c[8];  // NOLINT(modernize-avoid-c-arrays)
    strncpy(c, "hello1", sizeof(c));
    const auto [n, i] = interner.GetId(c);
    new2 = n;
    id2 = i;
    c[1] = 'g';
  }

  const auto [new3, id3] = interner.GetId("hello1");
  EXPECT_EQ(id1, id2);
  EXPECT_EQ(id1, id3);

  EXPECT_TRUE(new1);
  EXPECT_FALSE(new2);
  EXPECT_FALSE(new3);

  EXPECT_EQ(interner.Size(), 1);
}

}  // namespace cactus_rt::tracing::utils
