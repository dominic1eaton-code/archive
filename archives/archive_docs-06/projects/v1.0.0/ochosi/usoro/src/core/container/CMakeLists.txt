# @copyright
# @brief temporary test project
# @note
cmake_minimum_required(VERSION 3.18)
project(HesabuWindow)

# source files
list(
    APPEND PROJECT_SOURCES

    hwindow.cpp
)

# headers files
list(
    APPEND PROJECT_HEADERS
    
    # hbasewindow.h
    # hstructures.h
)

if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create libraries
if(BUILD_SHARED_LIBS)
    add_library(
        ${PROJECT_NAME} SHARED
        ${PROJECT_SOURCES}
        ${PROJECT_HEADERS}
    )
endif()

add_library(
    ${PROJECT_NAME}Lib STATIC
    ${PROJECT_SOURCES}
    ${PROJECT_HEADERS}
)

# includes
# target_include_directories(
#     ${PROJECT_NAME} PUBLIC
#     "${CMAKE_CURRENT_SOURCE_DIR}"
# )
target_include_directories(
    ${PROJECT_NAME}
    PUBLIC
    "$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>"
    "$<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>"
)

setup install target
common_install(
    ${PROJECT_NAME}
)

# Check if unit tests exist and enable accordingly
# global_check_unit_test()