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
function(common_setup_version PREFIX)
    # get version 
    message("retrieving current version, if any")

    # export variables
    set(${PREFIX}_VERSION       1.0.0   PARENT_SCOPE)
    set(${PREFIX}_VERSION_MAJOR 1       PARENT_SCOPE)
    set(${PREFIX}_VERSION_MINOR 0       PARENT_SCOPE)
    set(${PREFIX}_VERSION_PATCH 0       PARENT_SCOPE)
    set(${PREFIX}_VERSION_EXTRA 0       PARENT_SCOPE)
endfunction()

