# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Cmake project top level file
# @note : N/A
#-----------------------------------------------------------
# Project components
set(_logger Logger)
set(_utility Utility)

# add sub directories
add_subdirectory(${_logger})
