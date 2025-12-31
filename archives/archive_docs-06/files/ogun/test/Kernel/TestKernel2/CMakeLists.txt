#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)
project(TestKernel2)

# source files
list(
    APPEND PROJECT_SOURCE
    main.cpp
)

# headers files
list(
    APPEND PROJECT_HEADERS
)

# compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)
