# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Common defines for project
# @note : N/A
#-----------------------------------------------------------

# define root project directory
find_path(
    PROJECT_ROOT_PATH
    NAMES "project.cfg"
    PATHS ${CMAKE_HOME_DIRECTORY}
    DOC "root project directory"
)
get_filename_component(_devops_tool_path "${PROJECT_ROOT_PATH}/../DevopsTool" ABSOLUTE)

# define common cmake modules paths
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/common")
list(APPEND CMAKE_MODULE_PATH "${_devops_tool_path}/cmake/packages")

# define common cmake modules
include(globalSetupBuildEnvironment)  # Setup project build environment
include(globalSetupInstall)           # Setup project installation package
include(globalTargetLinkLibraries)    # Setup project enhanced link libraries functionality
include(globalFindPackage)            # Override find package functionality
include(globalSetupTest)              # Setup project global unit testing
include(globalInstall)                # Setup install function for project targets
include(globalDebug)                  # Setup project global debug features
include(dependencies)                 # Setup project external dependencies
include(install)                      # Setup project local install package
include(build)                        # Setup project local build environment
