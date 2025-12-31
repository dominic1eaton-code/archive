# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Project library file
# @note : N/A
#-----------------------------------------------------------
project(Graphics)

# components 
set(_device Device)

# list source files
list(
    APPEND PROJECT_SOURCE
    ${_device}/VulkanCommon.cpp
    ${_device}/VInstance.cpp
)

# list headers
list(
    APPEND PROJECT_HEADERS
    ${_device}/VulkanCommon.h
    ${_device}/VulkanConstants.h
    ${_device}/VulkanDefines.h
    ${_device}/VInstance.h
)

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create the library
add_library(
    ${PROJECT_NAME} SHARED
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)

# link dependencies
global_find_package(SDL2)
global_find_package(Vulkan)
global_find_package(LoggerCPP)
global_find_package(MathLib)
global_find_package(SystemLib)

# target features
target_compile_features(${PROJECT_NAME} PUBLIC cxx_std_17)

# include project headers for other projects using this library
target_include_directories(
    ${PROJECT_NAME} PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}"
)

# setup install targets
global_install(${PROJECT_NAME})

# check unit tests
# global_check_unit_tests()
