#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

#-----------------------------------------------------------
# @brief
# @note
#-----------------------------------------------------------
macro(common_configure_build_environment)
    if (WIN32)
        set(PROJECT_MOUNT C: CACHE STRING "Default project mount")
    elseif(UNIX)
        set(PROJECT_MOUNT ~ CACHE STRING "Default project mount")
    endif()

    # common environment variables
    set(PACKAGE_MANAGER_ROOT ${PROJECT_MOUNT}/global CACHE PATH "absolute path to location of packages on system")
    set(VERSION_INFO_FILE "versions.txt")

    message("-- Determining build system")
endmacro()