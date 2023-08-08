.PHONY: release debug build-test-debug test-debug test benchmark clean clean-all

ENABLE_CLANG_TIDY ?= OFF
ENABLE_TRACING ?= ON
ENABLE_EXAMPLES ?= ON
BUILD_DOCS ?= OFF
BUILD_TESTING ?= OFF
CMAKE_FLAGS := -DENABLE_CLANG_TIDY=$(ENABLE_CLANG_TIDY) -DENABLE_EXAMPLES=$(ENABLE_EXAMPLES) -DBUILD_DOCS=$(BUILD_DOCS) -DBUILD_TESTING=$(BUILD_TESTING) -DENABLE_TRACING=$(ENABLE_TRACING)

debug:
	cmake -Bbuild/$@ -DCMAKE_BUILD_TYPE=Debug $(CMAKE_FLAGS)
	cmake --build build/$@ -j $$(nproc)

release:
	cmake -Bbuild/$@ -DCMAKE_BUILD_TYPE=RelWithDebInfo $(CMAKE_FLAGS)
	cmake --build build/$@ -j $$(nproc)

build-test-debug:
	cmake -Bbuild/test -DCMAKE_BUILD_TYPE=Debug -DENABLE_EXAMPLES=OFF -DBUILD_TESTING=ON -DENABLE_CLANG_TIDY=$(ENABLE_CLANG_TIDY) -DENABLE_TRACING=$(ENABLE_TRACING)
	cmake --build build/test -j $$(nproc)

test-debug: build-test-debug
	ctest --test-dir build/test -V

test: test-debug

benchmark: build-test-debug
	build/test/tests/cactus_rt_tracing_benchmark

clean:
	test ! -d build/test || cmake --build build/test --target clean
	test ! -d build/debug || cmake --build build/debug --target clean
	test ! -d build/release || cmake --build build/release --target clean

clean-all:
	rm build -rf
