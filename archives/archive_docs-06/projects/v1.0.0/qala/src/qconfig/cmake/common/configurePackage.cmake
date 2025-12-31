# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Package configuration wrapper
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Package configuration wrapper
# @note : N/A
#-----------------------------------------------------------
macro(configure_package PACKAGE_NAME PACKAGE_VERSION PACKAGE_PATH PACKAGE_LIB_NAME PACKAGE_ENV_VAR)
    # ensure local download root path exists in downloads enabled
    if(PACKAGE_MANAGER_DONWLOADS_ENABLED)
        if(NOT DEFINED PACKAGE_MANAGER_ROOT)
            message(FATAL_ERROR "PACKAGE_MANAGER_ROOT must be defined")
        endif()
    endif()

    # set package paths
    set(_package_path ${PACKAGE_MANAGER_ROOT}/${PACKAGE_NAME}/${PACKAGE_VERSION})
    set(_package_root ${PACKAGE_NAME}_ROOT)
    string(TOUPPER ${_package_root} _package_root_upper)
    string(TOUPPER ${PACKAGE_NAME} _package_name_upper)

    # env variable
    set(ENV{${PACKAGE_ENV_VAR}} "${_package_path}")

    # create package 
    set(${PACKAGE_NAME}_LIBRARY_NAME ${PACKAGE_LIB_NAME} CACHE STRING "${PACKAGE_NAME} library name")
    set(${PACKAGE_NAME}_VERSION ${PACKAGE_VERSION} CACHE STRING "${PACKAGE_NAME} version")
    set(${PACKAGE_NAME}_PATH ${_package_path} CACHE STRING "${PACKAGE_NAME} path")
    set(${_package_root_upper} ${_package_path} CACHE STRING "${PACKAGE_NAME} root path")
    set(PACKAGE_${PACKAGE_NAME} ${${PACKAGE_NAME}_VERSION} CACHE STRING "${PACKAGE_NAME} iterable variable")
endmacro()
