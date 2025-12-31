# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Setup enhanced link library functionality
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Assert dependencies have been included before 
#         a target is used
# @note : Can be called in early project setup
# @usage: include(globalTargetLinkLibraries)
#         global_assert_dependencies(foo bar)
#-----------------------------------------------------------
macro(global_assert_dependencies)
    foreach(_arg ${ARGN})
        if(NOT ${_arg}_SOURCE_DIR)
            message(FATAL_ERROR
                    "The project ${_arg} must be added before '${PROJECT_NAME}'")
        endif()
    endforeach()
endmacro()

#-----------------------------------------------------------
# @brief: Assert depdencnies being linked against for target
#         have
# @note : Can be called in early project setup
# @usage: include(globalTargetLinkLibraries)
#         global_target_link_libraries(foo bar)
#-----------------------------------------------------------
macro(global_target_link_libraries)
    # Ensure libraries passed to be linked have been defined.
    # Failed assertion could lead to undefined behaviour for
    # included target.
    global_assert_dependencies(${ARGN})

    # set dependency runtime paths for unit test location
    # find functions
    foreach(_project IN ITEMS ${ARGN})
        get_target_property(_project_libraries ${_project} INTERFACE_LINK_LIBRARIES)
        get_target_property(_project_includes ${_project} INCLUDE_DIRECTORIES)
        list(
            APPEND _common_libraries
            ${_project_libraries}
        )
        list(
            APPEND _common_includes
            ${_project_includes}
        )
        list(REMOVE_DUPLICATES _common_libraries)
        list(REMOVE_DUPLICATES _common_includes)
    endforeach()
    list(FILTER  _common_libraries EXCLUDE REGEX ".*NOTFOUND.*")
    list(FILTER  _common_includes EXCLUDE REGEX ".*NOTFOUND.*")

    # libraries to link with
    message("${PROJECT_NAME} PUBLIC ${ARGN} ${_common_includes}")
    message("${PROJECT_NAME} ${ARGN} ${_common_libraries}")
    target_link_directories(${PROJECT_NAME} PRIVATE ${ARGN} ${_common_includes})
    target_link_libraries(${PROJECT_NAME} ${ARGN} ${_common_libraries})
endmacro()
