# @license
# @brief
cmake_minimum_required(VERSION 3.18)

# root
find_path(
    PROJECT_ROOT_PATH
    NAMES "project.qala"
    PATHS ${CMAKE_HOME_DIRECTORY}
    DOC "project root directory"
)

message("PROJECT_ROOT_PATH ${PROJECT_ROOT_PATH}")
message("CMAKE_HOME_DIRECTORY ${CMAKE_HOME_DIRECTORY}")

# cmake globals
set(PROJECT_MOUNT CACHE STRING "D:")
set(_cmake_globals_path PATH ABSOLUTE "${PROJECT_MOUNT}/dev/ws/qala-sf/src/dev/qala_cmake")
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/common")
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/packages")

# project includes
include(build)
