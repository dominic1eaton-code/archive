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
        
    # install(
    #     TARGETS ${PROJECT_NAME}
    #     EXPORT ${PROJECT_NAME}Targets
    #     LIBRARY DESTINATION  ${CMAKE_INSTALL_LIBDIR}
    #     ARCHIVE DESTINATION  ${CMAKE_INSTALL_LIBDIR}
    #     RUNTIME DESTINATION  ${CMAKE_INSTALL_BINDIR}
    #     INCLUDES DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
    # )

    # install(EXPORT ${PROJECT_NAME}Targets
    #         FILE ${PROJECT_NAME}Targets.cmake
    #         NAMESPACE ${CMAKE_PROJECT_NAME}::
    #         DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/${PROJECT_NAME}
    # )

    # # install config files
    # install(
    #     FILES ${PROJECT_CMAKE_PATH}/Find${PROJECT_NAME}.cmake
    #     COMPONENT "${PROJECT_NAME}"
    #     DESTINATION ${PROJECT_INSTALLATION_PATH}/lib
    # )

    # install header files
    install(
        DIRECTORY ${PROJECT_INCLUDE_PATH}/${CMAKE_PROJECT_NAME}
        COMPONENT "${PROJECT_NAME}"
        DESTINATION ${PROJECT_INSTALLATION_PATH}
    )
endmacro()
