#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

# Project components
set(_kernel Kernel)
set(_ui UI)

# add sub directories
add_subdirectory(${_kernel})
add_subdirectory(${_ui})
add_subdirectory(Controller)
add_subdirectory(Environment)
add_subdirectory(Model)
