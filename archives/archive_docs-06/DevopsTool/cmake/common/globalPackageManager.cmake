# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Setup cmake package dependency management.
# @note : N/A
#-----------------------------------------------------------

macro(setup_package_manager)
    # determine letter drive 
    set(PACKAGE_MANAGER_LETTER_DRIVE "F:" CACHE STRING "")

    # set common variables
    set(PACKAGE_MANAGER_ROOT_PATH "${PACKAGE_MANAGER_LETTER_DRIVE}/ots" CACHE STRING "")

    # check if server downloads are enabled
    set(PACKAGE_MANAGER_DONWLOADS_ENABLED ON CACHE BOOL "")

    # packages versions file
    set(VERSION_INFO_FILE "versions.info")
endmacro()
