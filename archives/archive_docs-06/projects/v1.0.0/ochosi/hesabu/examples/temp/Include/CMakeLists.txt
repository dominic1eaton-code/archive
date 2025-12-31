# @copyright
# @brief temporary test project
# @note
cmake_minimum_required(VERSION 3.18)
project(HesabuMain)

# source files
list(
    APPEND PROJECT_SOURCES
)

# headers files
list(
    APPEND PROJECT_HEADERS
    
    Hesabu.h
)

if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# # Create libraries
# if(BUILD_SHARED_LIBS)
#     add_library(
#         ${PROJECT_NAME} SHARED
#         ${PROJECT_SOURCES}
#         ${PROJECT_HEADERS}
#     )
# endif()

# add_library(
#     ${PROJECT_NAME}Lib STATIC
#     ${PROJECT_SOURCES}
#     ${PROJECT_HEADERS}
# )
add_library(
    ${PROJECT_NAME} INTERFACE
    ${PROJECT_HEADERS}
)
target_include_directories(${PROJECT_NAME} INTERFACE .)

# # includes
# target_include_directories(
#     ${PROJECT_NAME} PUBLIC
#     "${CMAKE_CURRENT_SOURCE_DIR}"
# )

# common_target_link_libraries(
#     HesabuWindowLib
# )

# # setup install target
# common_install(
#     ${PROJECT_NAME}
# )

# Check if unit tests exist and enable accordingly
# global_check_unit_test()