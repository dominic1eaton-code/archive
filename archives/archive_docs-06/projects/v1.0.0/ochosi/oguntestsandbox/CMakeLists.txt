# #-----------------------------------------------------------
# # @header DEFAULT
# # @brief
# # @note
# #-----------------------------------------------------------
# cmake_minimum_required(VERSION 3.18)
# project(Ogun)

# #include project cmake modules
# list(APPEND CMAKE_MODULE_PATH "${CMAKE_HOME_DIRECTORY}/cmake")
# include(project)

# # setup build environment
# # common_configure_build_environment()
# setup_build_environment()

# # setup installation targets
# # common_setup_install()
# setup_install()

# # setup dependendencies
# setup_dependencies()

# # include project source path(s)
# add_subdirectory("${PROJECT_SOURCE_PATH}")

# # setup unit tests
# add_subdirectory("${PROJECT_TEST_PATH}")
# # common_setup_unit_tests()
# # if(${UNIT_TESTS_ENABLED})
# #     common_add_unit_tests()
# # endif()

# # post build
# post_build()

#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
# @todo fix unit tests not building in debug mode
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)
project(OgunTestSandbox)

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
# set(ENABLE_UNIT_TEST TRUE CACHE BOOL "enable unit tests by default")
# global_setup_unit_test()
# # enable unit tests
# if(${BUILD_TESTS})
#     global_add_unit_tests()
# endif()
add_subdirectory("${PROJECT_TEST_PATH}")

# post build
post_build()