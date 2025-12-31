# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Common dependencies setup for project
# @note : N/A
#-----------------------------------------------------------
include(globalConfigurePackage)

#-----------------------------------------------------------
# @brief: Setup dependencies for project
# @note : N/A
#-----------------------------------------------------------
macro(project_setup_dependencies)
    # create versions file
    set(_versions_file ${CMAKE_BINARY_DIR}/${VERSION_INFO_FILE})
    file(WRITE "${_versions_file}" "")

    # package attribute variables
    set(_dependencies Gtest Vulkan SDL2 LoggerCPP GLM)
    set(_package_Gtest     1.12.2      ".")
    set(_package_Vulkan    1.3.204.0   ".")
    set(_package_SDL2      2.0.22      ".")
    set(_package_LoggerCPP 1.0.0       ".")
    set(_package_GLM       0.9.9       ".")

    # configure packages
    foreach(_dependency ${_dependencies})
        list(GET _package_${_dependency} 0 _version)
        list(GET _package_${_dependency} 1 _path)
        configure_package(${_dependency} ${_version} ${_path})
        file(APPEND "${_versions_file}" "${_dependency}=${_version}\n")
    endforeach()
endmacro()
