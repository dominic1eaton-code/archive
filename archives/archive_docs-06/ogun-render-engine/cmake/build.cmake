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
   
    # cmake configuration options
    option(BUILD_SHARED_LIBS "Build using shared libraries" ON)
    option(BUILD_TESTS "enable unit tests by default" ON)
    option(BUILD_VERBOSE "enable verbose cmake log messages" OFF)
    option(BUILD_EXAMPLES "Build example programs" ON)
    option(BUILD_BENCHMARKS "Build benchmarking programs" OFF)
 
    # define common project properties 
    set(PROJECT_ARCHITECTURE 64 CACHE STRING "Default project architecture")
    if (WIN32)
        set(PROJECT_MOUNT C: CACHE STRING "Default project mount")
        # define common compilation directives
        add_compile_definitions(OGUN_EXPORT)
        add_compile_definitions(PLATFORM_WINDOWS)
    elseif(UNIX)
        set(PROJECT_MOUNT ~ CACHE STRING "Default project mount")
        add_compile_definitions(PLATFORM_UNIX)
    endif()

    # define common paths
    set(PROJECT_SOURCE_PATH "${PROJECT_ROOT_PATH}/src" CACHE PATH "")
    set(PROJECT_TEST_PATH "${PROJECT_ROOT_PATH}/test" CACHE PATH "")
    set(PROJECT_INSTALLATION_PATH "${CMAKE_HOME_DIRECTORY}/${PROJECT_DEFAULT_INSTALLATION_PATH}")
    set(PROJECT_INSTALLATION_PREFIX "PROJECT" CACHE STRING "") 
endmacro()

