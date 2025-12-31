#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

# set mount
if (WIN32)
    set(PROJECT_MOUNT D: CACHE STRING "Default project mount")
elseif(UNIX)
    set(PROJECT_MOUNT ~ CACHE STRING "Default project mount")
endif()

# define project root directory
find_path(
    PROJECT_ROOT_PATH
    NAMES "project.cfg"
    PATHS ${CMAKE_HOME_DIRECTORY}
    DOC "project root directory"
)

# get DevOps tool properties
set(_devops_tool_path PATH ABSOLUTE "${PROJECT_MOUNT}/global/qala/1.0.0")
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/common")
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/packages")

# # include project cmake modules
include(configureArchitecture)
include(configureBuildEnvironment)
include(configureDebug)
include(configureInstall)
include(configureTargerLinkLibraries)
include(configureVersion)
include(configurePackage)
include(commonFindPackage)
include(setupInstall)
include(setupTest)
include(build)
include(dependencies)
include(install)
include(postbuild)