.PHONY: release debug clean clean-all

ENABLE_CLANG_TIDY ?= OFF
ENABLE_EXAMPLES ?= ON
BUILD_DOCS ?= OFF
BUILD_TESTING ?= OFF
CMAKE_FLAGS := -DENABLE_CLANG_TIDY=$(ENABLE_CLANG_TIDY) -DENABLE_EXAMPLES=$(ENABLE_EXAMPLES) -DBUILD_DOCS=$(BUILD_DOCS) -DBUILD_TESTING=$(BUILD_TESTING)

debug:
	cmake -Bbuild/$@ -DCMAKE_BUILD_TYPE=Debug $(CMAKE_FLAGS)
	cmake --build build/$@ -j $$(nproc)

release:
	cmake -Bbuild/$@ -DCMAKE_BUILD_TYPE=RelWithDebInfo $(CMAKE_FLAGS)
	cmake --build build/$@ -j $$(nproc)

clean:
	test ! -d build/debug || cmake --build build/debug --target clean
	test ! -d build/release || cmake --build build/release --target clean

clean-all:
	rm build -rf
