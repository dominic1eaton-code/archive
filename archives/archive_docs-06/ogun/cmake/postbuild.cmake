#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

#-----------------------------------------------------------
# @brief Setup project post build steps
# @note
#-----------------------------------------------------------
macro(post_build)
    # dump all build variables into file
    common_debug_dump_variables()
endmacro()
