# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: project unit test file
# @note : N/A
#-----------------------------------------------------------
project(RendererTest)

# list source files
list(
    APPEND PROJECT_SOURCE
    test.cpp
)

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create library
add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)

# install test targets
target_compile_features(${PROJECT_NAME} PUBLIC ${CPP_STD_VERSION})
global_install(
    ${PROJECT_NAME}
)