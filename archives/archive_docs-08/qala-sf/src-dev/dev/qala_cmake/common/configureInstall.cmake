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
function(common_install)
    # input args 
    set(_options "")
    set(_oneValueArgs ARCHIVE_DIR LIBRARY_DIR RUNTIME_DIR FILES_DIR LICENSE_DIR CONFIG_DIR SCRIPTS_DIR SEQUENCE_DIR)
    set(_multiValueArgs TARGETS EXECUTABLES FILES SOURCES HEADERS LICENSES CONFIG SCRIPTS SEQUENCE)
    cmake_parse_arguments(
        ARGS
        "${_options}"
        "${_oneValueArgs}"
        "${_multiValueArgs}"
        ${ARGN}
    )

    if(ARGS_UNPARSED_ARGUMENTS)
        # Treat unparsed arguments as targets
        set(ARGS_TARGETS "${ARGS_UNPARSED_ARGUMENTS}")
    endif()

    # verify targets have been passed to func
    if(NOT ARGS_TARGETS)
        message("-- NO TARGETS PASSED !")
    endif()

    # apply defaults 
    if(NOT ARGS_RUNTIME_DIR)
        set(ARGS_RUNTIME_DIR ${INSTALL_RUNTIME_SUBDIR})
    endif()
    message("INSTALL_RUNTIME_SUBDIR ${INSTALL_RUNTIME_SUBDIR}")
    message("ARGS_RUNTIME_DIR ${ARGS_RUNTIME_DIR}")
    message("ARGS_TARGETS ${ARGS_TARGETS}")

    # target install
    if(ARGS_TARGETS)
        if(UNIX)
            message("-- add library and archive install")
        else()
            if (BUILD_SHARED_LIBS)
                install(
                    TARGETS ${ARGS_TARGETS}
                    RUNTIME DESTINATION ${ARGS_RUNTIME_DIR}
                        COMPONENT RUNTIME
                        PERMISSIONS OWNER_WRITE OWNER_READ OWNER_EXECUTE
                                    GROUP_WRITE GROUP_READ GROUP_EXECUTE
                )
            endif()
            
            install(
                TARGETS ${ARGS_TARGETS}Lib
                RUNTIME DESTINATION ${ARGS_RUNTIME_DIR}
                    COMPONENT RUNTIME
                    PERMISSIONS OWNER_WRITE OWNER_READ OWNER_EXECUTE
                                GROUP_WRITE GROUP_READ GROUP_EXECUTE
            )
        endif()
    endif()
endfunction()
