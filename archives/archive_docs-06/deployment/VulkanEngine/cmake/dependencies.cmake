# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Common defines for project
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
    set(_dependencies Gtest)
    set(_package_Gtest     1.12.2      ".")

    # configure packages
    foreach(_dependency ${_dependencies})
        list(GET _package_${_dependency} 0 _version)
        list(GET _package_${_dependency} 1 _path)
        configure_package(${_dependency} ${_version} ${_path})
        file(APPEND "${_versions_file}" "${_dependency}=${_version}\n")
    endforeach()
endmacro()
