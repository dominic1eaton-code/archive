# ogun render renderer

## build
conan profile show default
conan profile path default
conan config home


Remove-Item -Path "build" -Recurse

rmdir /S/Q build
conan install . --output-folder=build --build=missing --profile=default
cd build
cmake .. -G "Visual Studio 18 2026" -DCMAKE_TOOLCHAIN_FILE=conan_toolchain.cmake
cmake --build . --config Release


conan install . --output-folder=build --build=missing --profile=debug
cmake --build . --config Debug


cmake .. -G "Visual Studio 17 2022" -DCMAKE_TOOLCHAIN_FILE=conan_toolchain.cmake
cmake .. -G "Visual Studio 17 2022" -DCMAKE_TOOLCHAIN_FILE=C:\dev\ws\oru-sdk\src\renderer\src\ogun\build\conan_toolchain.cmake