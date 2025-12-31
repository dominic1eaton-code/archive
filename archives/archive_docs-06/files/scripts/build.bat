rem
rem test build commands
rem

rem build logger
set BUILD_GENERATOR="Visual Studio 17"
set BUILD_GENERATOR="Visual Studio 17 2022"
set BUILD_PATH=build
set BUILD_PLATFORM=x64

cmake -G %BUILD_GENERATOR% -B %BUILD_PATH% -A %BUILD_PLATFORM% -DENABLE_UNIT_TEST=ON -DGTEST_ROOT="F:/ots/gtest/1.12.2"
cmake --build build
cmake --install build
cmake --install build --config Debug

rem build gtest
set BUILD_GENERATOR="Visual Studio 17 2022"
set BUILD_PATH=build
set BUILD_PLATFORM=x64
cmake -G %BUILD_GENERATOR% -B %BUILD_PATH% -A %BUILD_PLATFORM% -DCMAKE_INSTALL_PREFIX="F:/ots/gtest/1.12.2"  -DBUILD_SHARED_LIBS=ON
cmake --build build
cmake --install build --config Debug
