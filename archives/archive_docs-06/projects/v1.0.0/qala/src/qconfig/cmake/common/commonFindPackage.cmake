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
    # set(_multiValueArgs )
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
    target_include_directories(${PROJECT_NAME} PUBLIC ${${PACKAGE}_INCLUDE_DIR})
endmacro()
