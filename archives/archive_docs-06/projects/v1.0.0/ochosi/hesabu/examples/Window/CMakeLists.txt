# @copyright
# @brief temporary test project
# @note
cmake_minimum_required(VERSION 3.18)
project(HWindowExample)

# source files
list(
    APPEND PROJECT_SOURCES

    main.cpp
)

# headers files
list(
    APPEND PROJECT_HEADERS

)

if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create executable
add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCES}
    ${PROJECT_HEADERS}
)

# includes
target_include_directories(
    ${PROJECT_NAME} PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}"
)

common_target_link_libraries(
    HesabuWindowLib
)

# Check if unit tests exist and enable accordingly
# global_check_unit_test()