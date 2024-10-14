.PHONY: release debug build-test-debug test-debug test benchmark clean clean-all

CACTUS_RT_ENABLE_TRACING ?= ON
ENABLE_CLANG_TIDY ?= OFF
ENABLE_EXAMPLES ?= ON
BUILD_DOCS ?= OFF
BUILD_TESTING ?= OFF
CMAKE_FLAGS := -DENABLE_CLANG_TIDY=$(ENABLE_CLANG_TIDY) -DENABLE_EXAMPLES=$(ENABLE_EXAMPLES) -DBUILD_DOCS=$(BUILD_DOCS) -DBUILD_TESTING=$(BUILD_TESTING) -DCACTUS_RT_ENABLE_TRACING=$(CACTUS_RT_ENABLE_TRACING)

debug:
	cmake -Bbuild/$@ -DCMAKE_BUILD_TYPE=Debug $(CMAKE_FLAGS)
	cmake --build build/$@ -j $$(nproc)

release:
	cmake -Bbuild/$@ -DCMAKE_BUILD_TYPE=RelWithDebInfo $(CMAKE_FLAGS)
	cmake --build build/$@ -j $$(nproc)

build-test-debug:
	cmake -Bbuild/test -DCMAKE_BUILD_TYPE=Debug -DENABLE_EXAMPLES=OFF -DBUILD_TESTING=ON -DENABLE_CLANG_TIDY=$(ENABLE_CLANG_TIDY) -DCACTUS_RT_ENABLE_TRACING=$(CACTUS_RT_ENABLE_TRACING)
	cmake --build build/test -j $$(nproc)

test-debug: build-test-debug
	cd build/test && ctest -V

test: test-debug

build-test-release:
	cmake -Bbuild/benchmark -DCMAKE_BUILD_TYPE=RelWithDebInfo -DENABLE_EXAMPLES=OFF -DBUILD_TESTING=ON -DENABLE_CLANG_TIDY=$(ENABLE_CLANG_TIDY) -DCACTUS_RT_ENABLE_TRACING=$(CACTUS_RT_ENABLE_TRACING)
	cmake --build build/benchmark -j $$(nproc)

benchmark: build-test-release
	build/benchmark/tests/cactus_rt_tracing_benchmark

clean:
	test ! -d build/test || cmake --build build/test --target clean
	test ! -d build/benchmark || cmake --build build/benchmark --target clean
	test ! -d build/debug || cmake --build build/debug --target clean
	test ! -d build/release || cmake --build build/release --target clean

clean-all:
	rm build -rf
