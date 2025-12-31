# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Cmake project top level file
# @note : N/A
#-----------------------------------------------------------
project(VulkanEngine)

# Include project cmake modules 
list(APPEND CMAKE_MODULE_PATH "${CMAKE_HOME_DIRECTORY}/cmake")

# common includes
include(common)

# setup build environment 
global_setup_build_environment()
project_setup_build_environment()

# setup installation
global_define_install_directories()
global_install_clean_operation()

# project setup_dependencies
project_setup_dependencies()

# project source include directories
add_subdirectory("${PROJECT_SOURCE_PATH}")

# build installation target
project_setup_install()

# setup unit test
set(ENABLE_UNIT_TEST TRUE CACHE BOOL "enable unit tests by default")
global_setup_unit_test()

# enable unit tests
if(${ENABLE_UNIT_TEST})
    global_add_unit_tests()
endif()

# post analysis
global_debug_dump_variables()
