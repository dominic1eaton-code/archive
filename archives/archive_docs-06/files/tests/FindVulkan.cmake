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
set(Vulkan_VERSION "1.3.204.0")

# root directory
set(Vulkan_DIR "F:/ots/VulkanSDK/${Vulkan_VERSION}") 

# include directory 
set(Vulkan_INCLUDE_DIR "${Vulkan_DIR}/Include")
mark_as_advanced(Vulkan_INCLUDE_DIR)

# lib directory
set(Vulkan_LIBRARY_DIRS "${Vulkan_DIR}/Lib")

# lib file names 
set(_lib_names vulkan-1)

# find libraries
set(
    _find_options
    PATHS ${Vulkan_LIBRARY_DIRS}
    DOC "Location of vulkan library"
    NO_DEFAULT_PATH 
)

# find libraries to link wtih
foreach(_lib ${_lib_names})
    string(TOUPPER ${_lib} _libU)
    find_library(
        Vulkan_${_libU}_LIBRARY_RELEASE
        ${_lib}
        ${_find_options}
    )
    find_library(
        Vulkan_${_libU}_LIBRARY_DEBUG
        ${_lib}
        ${_find_options}
    )
    mark_as_advanced(
        Vulkan_${_libU}_LIBRARY_RELEASE
        Vulkan_${_libU}_LIBRARY_DEBUG
    )
    select_library_configurations(Vulkan_${_libU})
endforeach()

# combine libraries to single variable
unset(Vulkan_LIBRARY_LIST)
foreach(_lib ${_lib_names})
    string(TOUPPER ${_lib} _libU)
    list(APPEND Vulkan_LIBRARY_LIST ${Vulkan_${_libU}_LIBRARY})
endforeach()

# generate cmake variables
select_library_configurations(Vulkan)
find_package_handle_standard_args(
    Vulkan
    REQUIRED_VARS Vulkan_LIBRARY_LIST Vulkan_INCLUDE_DIR
    VERSION_VAR Vulkan_VERSION
)

# set found dirs
if(Vulkan_FOUND)
    set(Vulkan_INCLUDE_DIRS ${Vulkan_INCLUDE_DIR})
    set(Vulkan_LIBRARIES ${Vulkan_LIBRARY_LIST})
endif()