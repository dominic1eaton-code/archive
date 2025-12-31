#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

#-----------------------------------------------------------
# @brief Setup project build environment
# @note
#-----------------------------------------------------------
macro(setup_build_environment)
    # set language version
    set(CPP_STD_VERSION cxx_std_17 CACHE INTERNAL "")
    set(CMAKE_CXX_STANDARD 17)

    # define common compilation directives
    add_compile_definitions(OGUN_EXPORT)

    # define common project properties 
    set(PROJECT_ARCHITECTURE 64 CACHE STRING "Default project architecture")

    # define common paths
    set(PROJECT_SOURCE_PATH "${PROJECT_ROOT_PATH}/src" CACHE PATH "")
    set(PROJECT_TEST_PATH "${PROJECT_ROOT_PATH}/test" CACHE PATH "")
    set(PROJECT_INSTALLATION_PATH "${CMAKE_HOME_DIRECTORY}/${PROJECT_DEFAULT_INSTALLATION_PATH}")
    set(PROJECT_INSTALLATION_PREFIX "PROJECT" CACHE STRING "") 
endmacro()

