# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Setup common project installation package
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Define common set of installation directories
# @note : Can be called in early project setup
# @usage: include(globalSetupInstall)
#         global_define_install_directories()
#-----------------------------------------------------------
macro(global_define_install_directories)
    # top level common installation directory
    # set(PROJECT_DEFAULT_INSTALLATION_PATH "bin")
    set(PROJECT_DEFAULT_INSTALLATION_PREFIX "install" CACHE STRING "Default prefix path to install directory")

    set(PROJECT_INSTALL_RUNTIME_PATH "Release" CACHE STRING 
       "Default path from <PREFIX> to install RUNTIME targets")
    
    set(PROJECT_INSTALL_CONFIG_PATH "config" CACHE STRING 
       "Default path from <PREFIX> to install config targets")
    
    set(PROJECT_INSTALL_RELEASE_PATH "${PROJECT_INSTALL_RUNTIME_PATH}" CACHE STRING 
       "Default path from <PREFIX> to install binaries (dll, exe, pub) files")
       
    # Define install artifacts directory
    set(PROJECT_INSTALL_DIR "install" CACHE PATH 
        "Directory where build artifacts will be copied in preperation for creating installation package")

    set(CLEAN_INSTALL_PATH ON CACHE BOOL
        "When set to true, everythig in PROJECT_INSTALL_DIR will be deleted before install target in built")
    
    set(CMAKE_INSTALL_PREFIX "${PROJECT_INSTALL_DIR}" CACHE PATH
        "Override cmake install prefix" FORCE)
    mark_as_advanced(CMAKE_INSTALL_PREFIX)

    # Define package directory where archived (.zip, tar.gz, etc...) 
    # artifacts will be placed
    set(PROJECT_PACKAGE_PATH ${PROJECT_DEFAULT_INSTALLATION_PATH} CACHE STRING
        "Directory where packaged installation build artifact will be installed")
endmacro()

#-----------------------------------------------------------
# @brief: Define common set of installation properties
# @note : Can be called in early project setup
# @usage: include(globalSetupInstall)
#         global_define_install_properties()
#-----------------------------------------------------------
macro(global_define_install_properties)
    # set default install options
    set(INSTALL_OPTIONS INCLUDE_SUPPORT_FILES
                        INCLUDE_SOURCE_FILES
                        CACHE STRING
                        "Default build artifact install options")

    # enable default options 
    foreach(_option IN LISTS INSTALL_OPTIONS)
        set(${_option} TRUE CACHE BOOL "Default artifact installation option ${_option}")
        set_property(GLOBAL PROPERTY ${_option} TRUE)
    endforeach()

    # set default cpcack  options
    set(DEFAULT_CPACK_GENERATOR "ZIP" CACHE STRING "Default build artifact install options")
    set(DEFAULT_PROJECT_VENDOR "Project" CACHE STRING "Default build artifact install options")
    set(DEFAULT_PROJECT_VENDOR_PREFIX "Project" CACHE STRING "Default build artifact install options")

    # set default install props
    set(PROJECT_VERSION_MAJOR "1" CACHE STRING "Default version")
    set(PROJECT_VERSION_MINOR "0" CACHE STRING "Default version")
    set(PROJECT_VERSION_PATCH "0" CACHE STRING "Default version")
    set(PROJECT_VERSION_EXTRA "0" CACHE STRING "Default version")
    set(PROJECT_VERSION "${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}.${PROJECT_VERSION_PATCH}" CACHE STRING "Default version")
    set(PROJECT_PACKAGE_NAME "${CMAKE_PROJECT_NAME}" CACHE STRING "Default package name")
    set(PROJECT_PACKAGE_FILE_NAME "${PROJECT_PACKAGE_NAME}-${PROJECT_VERSION}" CACHE STRING "Default package name")
endmacro()

#-----------------------------------------------------------
# @brief: Setup install package
# @note : Can be called in early project setup
# @usage: include(setupInstall)
#         common_setup_install()
#-----------------------------------------------------------
macro(common_setup_install)
    # set default properties
    global_define_install_properties()

    # set default directories
    global_define_install_directories()

    # set Cpack variables
    # https://cmake.org/cmake/help/latest/cpack_gen/archive.html
    set(CPACK_GENERATOR ${DEFAULT_CPACK_GENERATOR})

    # set package name
    set(CPACK_PACKAGE_NAME ${PROJECT_PACKAGE_NAME})

    # set package to install and corresponding package label
    set(CPACK_PACKAGE_EXECUTABLES ${EXE_NAME};${PROJECT_PACKAGE_NAME})

    # Do not include package name as root directory of generated archive file
    set(CPACK_INCLUDE_TOPLEVEL_DIRECTORY 0)

    # set vendor
    set(CPACK_PACKAGE_VENDOR "${DEFAULT_PROJECT_VENDOR}")

    # set version
    set(CPACK_PACKAGE_VERSION "${PROJECT_VERSION}")

    # set generate archive file name
    set(CPACK_PACKAGE_FILE_NAME "${PROJECT_PACKAGE_FILE_NAME}")

    # must always include cpack last to complete configuration
    include(CPack)
endmacro()

#-----------------------------------------------------------
# @brief: Setup install clean package operation
# @note : Can be called in early project setup
# @usage: include(globalSetupInstall)
#         global_install_clean_operation()
#-----------------------------------------------------------
macro(global_install_clean_operation)

endmacro()