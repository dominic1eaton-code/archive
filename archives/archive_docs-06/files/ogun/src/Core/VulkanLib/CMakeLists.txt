# @header 
# @copyright
# @brief
# @note
cmake_minimum_required(VERSION 3.18)
project(VulkanLib)

set(_kernel Kernel)

# source files
list(
    APPEND PROJECT_SOURCES

    ${_kernel}/VKernel.cpp
)

# headers files
list(
    APPEND PROJECT_HEADERS
    
    ${_kernel}/VKernel.h
)

# compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

add_library(
    ${PROJECT_NAME} SHARED
    ${PROJECT_SOURCES}
    ${PROJECT_HEADERS}
)

# Link dependencies.
set(ENV{VULKAN_SDK} "C:/global/VulkanSDK/1.3.296.0")
set(CMAKE_CXX_STANDARD 17)
find_package(Vulkan REQUIRED)
target_link_libraries(${PROJECT_NAME} Vulkan::Vulkan)
target_include_directories(${PROJECT_NAME} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/${_src})
