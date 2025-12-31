# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Setup Wrap find package functionality
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Wrap find package functionality
# @note : N/a
# @usage: include(globalFindPackage)
#         global_find_package(PACKAGE)
#-----------------------------------------------------------
macro(global_find_package PACKAGE)
    # find package
    find_package(${PACKAGE} ${ARGN} REQUIRED)

    # include package directories
    include_directories(${${PACKAGE}_INCLUDE_DIR})

    # include package definitions
    add_definitions(${${PACKAGE}_DEFINITIONS})

    # link package libraries
    message("PROJECT_NAME ${PROJECT_NAME} ${${PACKAGE}_LIBRARY}")
    target_link_libraries(${PROJECT_NAME} ${${PACKAGE}_LIBRARY})
endmacro()
