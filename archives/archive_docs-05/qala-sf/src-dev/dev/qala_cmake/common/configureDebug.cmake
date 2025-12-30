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
macro(common_debug_dump_variables)
    file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/AllVariables.txt "")
    get_cmake_property(_vars_list VARIABLES)
    foreach(_ivar ${_vars_list})
        file(APPEND ${CMAKE_CURRENT_BINARY_DIR}/AllVariables.txt "${_ivar} \"${${_ivar}}\"\n")
    endforeach()
endmacro()