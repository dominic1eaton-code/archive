#-----------------------------------------------------------
# @copyright
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)
project(hesabu)

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

# project includes
include_directories(include)

# include project source path(s)
add_subdirectory("${PROJECT_SOURCE_PATH}")

# include example programs
if(${BUILD_EXAMPLES})
    add_subdirectory(examples)
endif()

# include benchmarks
if(${BUILD_BENCHMARKS})
    add_subdirectory(benchmarks)
endif()

# setup and enable unit tests
# global_setup_unit_test()
# if(${BUILD_TESTS})
#     global_add_unit_tests()
# endif()

# post build
post_build()