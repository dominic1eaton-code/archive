# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief
# @description
# @note
#-----------------------------------------------------------
macro(common_find_package PACKAGE)
    # input args 
    set(_options "")
    set(_oneValueArgs NO_LIB)
    set(_multiValueArgs "")
    cmake_parse_arguments(
        ARGS
        "${_options}"
        "${_oneValueArgs}"
        "${_multiValueArgs}"
        ${ARGN}
    )

    find_package(${PACKAGE} ${ARGN} REQUIRED)
    add_definitions(${${PACKAGE}_DEFINITIONS})
    if(NOT "${${PACKAGE}_LIBRARY}" STREQUAL "NONE")
        target_link_libraries(${PROJECT_NAME} ${PACKAGE}::${${PACKAGE}_LIBRARY_NAME})
    endif()
    if (BUILD_VERBOSE)
        message("-- DEBUG ${PROJECT_NAME} PUBLIC ${${PACKAGE}_INCLUDE_DIR}")
        message("-- DEBUBUILD_VERBOSEG ${PACKAGE}_INCLUDE_DIR ${${PACKAGE}_INCLUDE_DIR} ")
        message("-- DEBUG PROJECT_NAME ${PROJECT_NAME} ")
        message("-- DEBUG PACKAGE ${PACKAGE} ")
        message("-- DEBUG target_type ${target_type} ")
    endif()
    # include as executable
    get_target_property(target_type ${PROJECT_NAME} TYPE)
    if (target_type STREQUAL "EXECUTABLE")
        target_include_directories(${PROJECT_NAME} PUBLIC "${${PACKAGE}_INCLUDE_DIR}")
    else()
    # includes as library
        if (BUILD_SHARED_LIBS)
            target_include_directories(${PROJECT_NAME} PUBLIC "${${PACKAGE}_INCLUDE_DIR}")
        endif()
        target_include_directories(${PROJECT_NAME}Lib PUBLIC "${${PACKAGE}_INCLUDE_DIR}")
    endif()
endmacro()
