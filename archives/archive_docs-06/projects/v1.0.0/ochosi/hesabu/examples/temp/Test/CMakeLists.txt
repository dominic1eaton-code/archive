# @copyright
# @brief temporary test project
# @note
cmake_minimum_required(VERSION 3.18)
project(HesabuWindow)

# source files
list(
    APPEND PROJECT_SOURCES

    linux_main.cpp
    
)

# headers files
list(
    APPEND PROJECT_HEADERS
    
)

if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCES}
    ${PROJECT_HEADERS}
)

if (UNIX)
    find_package(X11 REQUIRED)
    target_include_directories(${PROJECT_NAME} PUBLIC ${X11_INCLUDE_DIR})
    target_link_libraries(${PROJECT_NAME} ${X11_LIBRARIES})
endif()

# # Create library
# if(BUILD_SHARED_LIBS)
#     add_library(
#         ${PROJECT_NAME} SHARED
#         ${PROJECT_SOURCES}
#         ${PROJECT_HEADERS}
#     )
# else()
#     add_library(
#         ${PROJECT_NAME}Lib STATIC
#         ${PROJECT_SOURCES}
#         ${PROJECT_HEADERS}
#     )
# endif()

# Check if unit tests exist and enable accordingly
global_check_unit_test()