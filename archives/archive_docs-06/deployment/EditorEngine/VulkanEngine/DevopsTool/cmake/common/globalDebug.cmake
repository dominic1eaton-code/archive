# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Setup debug functionality
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Dump all variable from cmake generation in file
# @note : N/a
# @usage: include(globalDebug)
#         global_debug_dump_variables(PACKAGE)
#-----------------------------------------------------------
macro(global_debug_dump_variables)
    # define default debug variables file
    set(PROJECT_DEFAULT_VARIABLES_DEBUG_FILE "AllVariables.txt"
        CACHE STRING "Default debug variables file")

    # write cmake variables to file
    file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_DEFAULT_VARIABLES_DEBUG_FILE} "")
    get_cmake_property(_vars_list VARIABLES)
    foreach(_ivar ${_vars_list})
        file(APPEND ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_DEFAULT_VARIABLES_DEBUG_FILE} "${_ivar} \"${${_ivar}}\"\n")
    endforeach()
endmacro()
