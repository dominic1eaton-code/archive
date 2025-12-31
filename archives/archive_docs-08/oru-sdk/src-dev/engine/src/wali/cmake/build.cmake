# @license
# @brief
cmake_minimum_required(VERSION 3.18)

# @brief configure build environment
macro(configure_environment)
    # qconfigure_environment()
    set(PROJECT_SOURCE_PATH "${PROJECT_ROOT_PATH}/src" CACHE PATH "project sources path")
endmacro()

macro(configure_source)
    add_subdirectory("${PROJECT_SOURCE_PATH}")
endmacro()

macro(configure_tests)
    # qconfigure_tests()
    message("qconfigure_tests")
    if(${BUILD_TESTS})
        # qadd_tests()
        message("qadd_tests")
    endif()

    # qconfigure_sasta()
    message("qconfigure_sasta")
endmacro()

macro(post_build)
    message("post build")
endmacro()


macro(configure_install)
    message("configure_install")
endmacro()

macro(configure_globals)
    # qdump_debug_variables()
    message("qdump_debug_variables")
endmacro()