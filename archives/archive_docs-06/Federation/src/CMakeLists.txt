# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Add project source sub folders
# @note : N/A
#-----------------------------------------------------------
# Engine components
set(_engine  Engine)
set(_editor  Editor)
set(_systems Systems)

# add component directories
# engine
add_subdirectory(${_engine})

# editor
add_subdirectory(${_editor})

# systems
add_subdirectory(${_systems}/Audio)
add_subdirectory(${_systems}/Core)
add_subdirectory(${_systems}/Render)
