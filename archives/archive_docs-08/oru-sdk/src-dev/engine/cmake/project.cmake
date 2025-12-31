# @license
# @brief
cmake_minimum_required(VERSION 3.18)

# find project root
find_path(
    PROJECT_ROOT
    NAMES "project.qala"
    PATHS ${CMAKE_HOME_DIRECTORY}
    DOC "project root directory"
)
list(APPEND CMAKE_MODULE_PATH "")

# includes
include(build)
include(globals)
include(install)
include(post)