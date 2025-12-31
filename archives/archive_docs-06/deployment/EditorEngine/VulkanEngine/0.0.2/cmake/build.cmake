# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Common defines for project
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Setup build environment for project
# @note : N/A
#-----------------------------------------------------------
macro(project_setup_build_environment)
    # set language version
    set(CPP_STD_VERSION cxx_std_17 CACHE INTERNAL "")

    # define common compilation directives
    add_compile_definitions(LOGGER_EXPORT)

    # define common variables 
    set(PROJECT_ARCHITECTURE 64 CACHE STRING "Default project architecture")

    # define common paths
    set(PROJECT_SOURCE_PATH "${PROJECT_ROOT_PATH}/src" CACHE PATH "")
    set(PROJECT_TEST_PATH "${PROJECT_ROOT_PATH}/tests" CACHE PATH "")
    set(PROJECT_INSTALLATION_PATH "${CMAKE_HOME_DIRECTORY}/${PROJECT_DEFAULT_INSTALLATION_PATH}")
    set(PROJECT_INSTALLATION_PREFIX "PROJECT" CACHE STRING "")
endmacro()
