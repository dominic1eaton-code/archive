# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Common defines for project
# @note : N/A
#-----------------------------------------------------------
include(globalSetupInstall)

#-----------------------------------------------------------
# @brief: Setup install for project
# @note : N/A
#-----------------------------------------------------------
macro(project_setup_install)
    global_setup_install()
endmacro()
