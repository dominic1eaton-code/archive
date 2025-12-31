# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Add project source sub folders
# @note : N/A
#-----------------------------------------------------------
project(Audio)

# list source files
list(
    APPEND PROJECT_SOURCE
    AudioSystem.cpp
)

# list headers
list(
    APPEND PROJECT_HEADERS
    AudioSystem.h
)

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create the executable
add_library(
    ${PROJECT_NAME} SHARED
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)

# target features
target_compile_features(${PROJECT_NAME} PUBLIC cxx_std_17)

# setup install targets
global_install(${PROJECT_NAME})

# # check unit tests
# global_check_unit_tests()
