# @header 
# @copyright
# @brief
# @note
cmake_minimum_required(VERSION 3.18)
project(NoiseTest)

# source files
list(
    APPEND PROJECT_SOURCES
    
    main.cpp
)

# headers files
list(
    APPEND PROJECT_HEADERS

)

# compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O3
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
endif()

add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCES}
    ${PROJECT_HEADERS}
)

# add dependencies
common_find_package(Vulkan)
common_find_package(STB)
common_find_package(Eigen3)
common_find_package(glm)
