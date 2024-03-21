#include <benchmark/benchmark.h>
#include <cactus_rt/tracing/utils/string_interner.h>

namespace {
// The for (auto _ : state) triggers the following rule...
// NOLINTBEGIN(clang-analyzer-deadcode.DeadStores)
using cactus_rt::tracing::utils::StringInterner;

StringInterner SetupInterner() {
  StringInterner interner;
  interner.GetId("hello1");
  interner.GetId("hello2");
  interner.GetId("hello3");
  interner.GetId("hello4");
  interner.GetId("hello5");
  interner.GetId("hello6");
  interner.GetId("hello7");
  interner.GetId("hello8");
  interner.GetId("hello9");
  return interner;
}

void BM_StringInternerConstCharArr(benchmark::State& state) {
  auto interner = SetupInterner();

  for (auto _ : state) {
    interner.GetId("hello1");
  }
}
BENCHMARK(BM_StringInternerConstCharArr);

void BM_StringInternerStdLongString(benchmark::State& state) {
  auto        interner = SetupInterner();
  std::string s;
  for (int i = 0; i < 500; i++) {
    s.append("hello ");
  }

  for (auto _ : state) {
    interner.GetId(s);
  }
}
BENCHMARK(BM_StringInternerStdLongString);
// NOLINTEND(clang-analyzer-deadcode.DeadStores)
}  // namespace
