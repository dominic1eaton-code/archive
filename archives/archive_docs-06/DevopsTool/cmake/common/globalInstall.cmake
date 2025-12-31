# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: package install functionality
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Global package install function
# @note : N/a
# @usage: include(globalDebug)
#         global_debug_dump_variables(PACKAGE)
#-----------------------------------------------------------
function(global_install)
    # parse input args
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

    # Treat unparsed arguments as targets
    if(ARGS_UNPARSED_ARGUMENTS)
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

    # install targets
    if(ARGS_TARGETS)
        if(UNIX)
            message("-- add library and archive install")
        else()
            install(
                TARGETS ${ARGS_TARGETS}
                RUNTIME DESTINATION ${ARGS_RUNTIME_DIR}
                    COMPONENT RUNTIME
                    PERMISSIONS OWNER_WRITE OWNER_READ OWNER_EXECUTE
                                GROUP_WRITE GROUP_READ GROUP_EXECUTE
            )
        endif()
    endif()
endfunction()