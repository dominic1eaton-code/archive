# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Cmake project top level file
# @note : N/A
#-----------------------------------------------------------
project(Project1)

set(PROJECT_NAME_LIB  "${PROJECT_NAME}Lib" CACHE STRING "Name of project library created")
set(PROJECT_NAME_TEST "${PROJECT_NAME}Test" CACHE STRING "Name of project test exectuable created")

# list source files
list(
    APPEND PROJECT_SOURCE
    Project1.cpp
)

# list headers
list(
    APPEND PROJECT_HEADERS
    Project1.h
)

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()


# Create library
add_library(
    ${PROJECT_NAME_LIB} SHARED
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)

# target features
target_compile_features(${PROJECT_NAME_LIB} PUBLIC cxx_std_17)

# enable/include project lib unit tests
# Create test executable

# list source files
list(
    APPEND PROJECT_SOURCE_TEST
    tests/TestProject1.cpp
    tests/main.cpp 
)

add_executable(
    ${PROJECT_NAME_TEST}
    ${PROJECT_SOURCE_TEST} # Unit test source code
    ${PROJECT_SOURCE}      # Unit test lbrary under test source code
)

# link library under test
#target_link_libraries(${PROJECT_NAME_TEST} ${PROJECT_NAME_LIB})

# find, link and include unit test tools
set(GTEST_ROOT "F:/ots/gtest/1.12.2")
find_package(GTest REQUIRED)
include(GoogleTest)
include_directories(${GTEST_INCLUDE_DIR})
target_link_libraries(${PROJECT_NAME_TEST} PRIVATE GTest::gtest GTest::gtest_main)
#target_link_libraries(${PROJECT_NAME_TEST} ${GTEST_LIBRARY} ${GTEST_MAIN_LIBRARY})
#target_link_libraries(${PROJECT_NAME_TEST} gtest gtest_main)

# tell cmake to enable unit tests
enable_testing()
add_test(
    NAME ${PROJECT_NAME_TEST} 
    COMMAND ${PROJECT_NAME_TEST}
)