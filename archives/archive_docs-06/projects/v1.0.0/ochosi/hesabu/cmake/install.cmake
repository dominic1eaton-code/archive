# @copyright
# @brief
# @note
cmake_minimum_required(VERSION 3.18)

#-----------------------------------------------------------
# @brief Setup project installation targets
# @note
#-----------------------------------------------------------
macro(setup_install)
    # setup cmake package file descriptors
    include(CMakePackageConfigHelpers)
    set(targets_export_name ${PROJECT_CMAKE_PACKAGE_NAME}Targets CACHE INTERNAL "")
    set(generated_dir "${CMAKE_CURRENT_BINARY_DIR}/generated" CACHE INTERNAL "")
    set(cmake_files_install_dir "${CMAKE_INSTALL_LIBDIR}/cmake/${PROJECT_CMAKE_PACKAGE_NAME}")
    set(version_file "${generated_dir}/${PROJECT_CMAKE_PACKAGE_NAME}ConfigVersion.cmake")
    
    # write_basic_package_version_file(${version_file} VERSION ${PROJECT_VERSION} COMPATIBILITY AnyNewerVersion)

    # install(EXPORT ${targets_export_name}
    #     COMPONENT "${PROJECT_NAME}"
    #     NAMESPACE ${PROJECT_CMAKE_PACKAGE_NAME}::
    #     DESTINATION ${cmake_files_install_dir}
    # )

    set(config_file "${generated_dir}/${PROJECT_CMAKE_PACKAGE_NAME}Config.cmake")
    # configure_package_config_file(
    #     "${gtest_SOURCE_DIR}/cmake/Config.cmake.in"
    #     "${config_file}" INSTALL_DESTINATION ${cmake_files_install_dir}
    # )

    # install(FILES ${version_file} ${config_file}
    #     COMPONENT "${PROJECT_NAME}"
    #     DESTINATION ${cmake_files_install_dir}
    # )

    # install config files
    install(
        FILES ${PROJECT_CMAKE_PATH}/FindHesabu.cmake
        COMPONENT "${PROJECT_NAME}"
        DESTINATION ${PROJECT_INSTALLATION_PATH}/lib
    )

    # install header files
    install(
        DIRECTORY ${PROJECT_INCLUDE_PATH}/${CMAKE_PROJECT_NAME}
        COMPONENT "${PROJECT_NAME}"
        DESTINATION ${PROJECT_INSTALLATION_PATH}
    )
endmacro()
