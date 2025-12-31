# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Cmake project top level file
# @note : N/A
#-----------------------------------------------------------
project(Logger)

# list source files
list(
    APPEND PROJECT_SOURCE
    Logger.cpp
)

# list headers
list(
    APPEND PROJECT_HEADERS
    Logger.h
    LoggerDefines.h
)

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create library
add_library(
    ${PROJECT_NAME} SHARED
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)

# target features
target_compile_features(${PROJECT_NAME} PUBLIC cxx_std_17)

target_include_directories(
    ${PROJECT_NAME}
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}"
)

# setup install targets
global_install(
    ${PROJECT_NAME}
)

# install header files include
install(
    DIRECTORY   "${CMAKE_CURRENT_SOURCE_DIR}/"
    DESTINATION "${CMAKE_HOME_DIRECTORY}/${CMAKE_INSTALL_PREFIX}/include/"
    FILES_MATCHING PATTERN "*.h"
)

# Check if unit tests exist and enable accordingly
global_check_tests_exist()