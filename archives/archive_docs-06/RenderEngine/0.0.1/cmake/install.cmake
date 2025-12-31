# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Common installation setup for project
# @note : N/A
#-----------------------------------------------------------
include(globalSetupInstall)

#-----------------------------------------------------------
# @brief: Setup install for project
# @note : N/A
#-----------------------------------------------------------
macro(project_setup_install)
    project_install_support_files()
    global_setup_install()
endmacro()

#-----------------------------------------------------------
# @brief: Install project supporting files
# @note : N/A
#-----------------------------------------------------------
macro(project_install_support_files)
    install(
        FILES
            ${CMAKE_HOME_DIRECTORY}/project.cfg
        DESTINATION "."
        COMPONENT   SUPPORT_FILES
        PERMISSIONS OWNER_WRITE OWNER_READ OWNER_EXECUTE
                    GROUP_WRITE GROUP_READ GROUP_EXECUTE)
endmacro()
