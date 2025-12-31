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
macro(common_target_link_libraries)
    message("-- common_target_link_libraries")

    # check libraries have been defined
    # global_assert_dependent_projects(${ARGN})

    # set dependency runtime paths for unit test location find functions
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
    target_link_directories(${PROJECT_NAME} PUBLIC ${ARGN} ${_common_includes})
    target_link_libraries(${PROJECT_NAME} ${ARGN} ${_common_libraries})
endmacro()

#-----------------------------------------------------------
# @brief
# @note
#-----------------------------------------------------------
function(common_assert_dependent_projects)
    foreach(_arg ${ARGN})
        if(NOT ${_arg}_SOURCE_PATH)
            message("-- not defined ${_arg}_SOURCE_PATH")
        endif()
    endforeach()
endfunction()