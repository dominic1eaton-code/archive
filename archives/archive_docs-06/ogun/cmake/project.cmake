#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

# define project root directory
find_path(
    PROJECT_ROOT_PATH
    NAMES "project.cfg"
    PATHS ${CMAKE_HOME_DIRECTORY}
    DOC "project root directory"
)

# get DevOps tool properties
# set(_devops_platform "qala")
# set(_devops_tool "devTool")
# get_filename_component(_devops_tool_path "${PROJECT_ROOT_PATH}/../${_devops_platform}/${_devops_tool}" ABSOLUTE)
# message("devops tool path: ${_devops_tool_path}")
set(_devops_tool_path PATH ABSOLUTE  "D:/global/qala/1.0.0")
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/common")
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/packages")

# # include project cmake modules
include(configureArchitecture)
include(configureBuildSystem)
include(configureCPack)
include(configureDebug)
include(configureInstall)
include(configureTargerLinkLibraries)
include(configureVersion)
include(build)
include(dependencies)
include(install)
include(postbuild)