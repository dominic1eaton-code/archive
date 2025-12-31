# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Add project source sub folders
# @note : N/A
#-----------------------------------------------------------
# Engine components
set(_renderer Renderer)

# libraries
add_subdirectory(${_renderer}/Devices)
add_subdirectory(${_renderer}/Graphics)
