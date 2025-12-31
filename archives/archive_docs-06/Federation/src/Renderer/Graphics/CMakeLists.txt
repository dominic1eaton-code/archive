# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Project library file
# @note : N/A
#-----------------------------------------------------------
project(Graphics)

# project components
set(_devices  Devices)
set(_buffer   Buffer)

# list source files
list(
    APPEND PROJECT_SOURCE
    ${_devices}/VInstance.cpp
    ${_devices}/PhysicalDevice.cpp
    ${_devices}/VWindow.cpp
    ${_devices}/LogicalDevice.cpp
    graphics_test_main.cpp
)

# list headers
list(
    APPEND PROJECT_HEADERS
    ${_devices}/VInstance.h
    ${_devices}/PhysicalDevice.h
    ${_devices}/VWindow.h
    ${_devices}/LogicalDevice.h
)

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create the library
add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)
# add_library(
#     ${PROJECT_NAME} SHARED
#     ${PROJECT_SOURCE}
#     ${PROJECT_HEADERS}
# )

# link dependencies
global_find_package(Vulkan)
global_find_package(LoggerCPP)
global_find_package(SDL2)

# target features
target_compile_features(${PROJECT_NAME} PUBLIC cxx_std_17)

# setup install targets
global_install(${PROJECT_NAME})

# # check unit tests
# global_check_unit_tests()
