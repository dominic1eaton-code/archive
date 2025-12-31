# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief
# @description
# @note
#-----------------------------------------------------------
include(FindPackageHandleStandardArgs)
include(SelectLibraryConfigurations)

# version 
set(GLFW_VERSION "3.3.6")

# root directory
set(GLFW_DIR "F:/ots/glfw/${GLFW_VERSION}/x64") 

# include directory 
set(GLFW_INCLUDE_DIR "${GLFW_DIR}/Include")
mark_as_advanced(GLFW_INCLUDE_DIR)

# lib directory
set(GLFW_LIBRARY_DIRS "${GLFW_DIR}/bin")

# lib file names 
set(_lib_names glfw3dll)

# find libraries
set(
    _find_options
    PATHS ${GLFW_LIBRARY_DIRS}
    DOC "Location of GLFW library"
    NO_DEFAULT_PATH 
)

# find libraries to link wtih
foreach(_lib ${_lib_names})
    string(TOUPPER ${_lib} _libU)
    find_library(
        GLFW_${_libU}_LIBRARY_RELEASE
        ${_lib}
        ${_find_options}
    )
    find_library(
        GLFW_${_libU}_LIBRARY_DEBUG
        ${_lib}
        ${_find_options}
    )
    mark_as_advanced(
        GLFW_${_libU}_LIBRARY_RELEASE
        GLFW_${_libU}_LIBRARY_DEBUG
    )
    select_library_configurations(GLFW_${_libU})
endforeach()

# combine libraries to single variable
unset(GLFW_LIBRARY_LIST)
foreach(_lib ${_lib_names})
    string(TOUPPER ${_lib} _libU)
    list(APPEND GLFW_LIBRARY_LIST ${GLFW_${_libU}_LIBRARY})
endforeach()

# generate cmake variables
select_library_configurations(GLFW)
find_package_handle_standard_args(
    GLFW
    REQUIRED_VARS GLFW_LIBRARY_LIST GLFW_INCLUDE_DIR
    VERSION_VAR GLFW_VERSION
)

# set found dirs
if(GLFW_FOUND)
    set(GLFW_INCLUDE_DIRS ${GLFW_INCLUDE_DIR})
    set(GLFW_LIBRARIES ${GLFW_LIBRARY_LIST})
endif()