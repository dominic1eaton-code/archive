# overview
logging unit for cpp

## deps
https://ccache.dev/download.html

## Building 

 set BUILD_GENERATOR="Ninja"
 set BUILD_GENERATOR="Visual Studio 17 2022"
 set BUILD_PATH=build
 set BUILD_PLATFORM=x64
 
 cmake -G %BUILD_GENERATOR% -B %BUILD_PATH% -A %BUILD_PLATFORM% -DENABLE_UNIT_TEST=ON -DGTEST_ROOT="F:/ots/gtest/1.12.2"
 cmake -G %BUILD_GENERATOR% -B %BUILD_PATH%
 cmake --build build
 cmake --install build --config Debug
 cmake --build build --target package

 cd build
 ctest
 ctest --output-junit testfile.xml
 
 C:\Users\domni\AppData\Roaming\Code\User\settings.json