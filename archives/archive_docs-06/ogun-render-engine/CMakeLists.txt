#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
# @todo fix unit tests not building in debug mode
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)
project(OgunEngine)

#include project cmake modules
list(APPEND CMAKE_MODULE_PATH "${CMAKE_HOME_DIRECTORY}/cmake")
include(project)

# setup build environment
common_configure_build_environment()
setup_build_environment()

# setup installation targets
common_setup_install()
setup_install()

# setup dependendencies
setup_dependencies()

# include project source path(s)
add_subdirectory("${PROJECT_SOURCE_PATH}")

# setup unit test
global_setup_unit_test()
if(${BUILD_TESTS})
    global_add_unit_tests()
endif()

# post build
post_build()