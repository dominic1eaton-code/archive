# @copyright
# @brief
# @note
# @input
#       Usoro_ROOT
# @output
#
cmake_minimum_required(VERSION 3.18)
include(FindPackageHandleStandardArgs)
include(SelectLibraryConfigurations)

set(PACKAGE_NAME Usoro)
string(TOUPPER ${PACKAGE_NAME} UPACKAGE_NAME)
string(TOLOWER ${PACKAGE_NAME} LPACKAGE_NAME)
# set(${PACKAGE_NAME}_DIR ${${UPACKAGE_NAME}_ROOT})
# set(${PACKAGE_NAME}_DIR ${${UPACKAGE_NAME}_PATH})
set(${PACKAGE_NAME}_DIR ${${PACKAGE_NAME}_PATH})
set(${PACKAGE_NAME}_LIBRARY_DIR ${${PACKAGE_NAME}_DIR}/lib)
set(${PACKAGE_NAME}_INCLUDE_DIR ${${PACKAGE_NAME}_DIR}/include)

# find includes
set(_include ${LPACKAGE_NAME}.h)
find_path(
    ${PACKAGE_NAME}_INCLUDE_DIR
    NAMES ${_include}
    PATHS ${${PACKAGE_NAME}_INCLUDE_DIR}/${LPACKAGE_NAME}
    DOC "Location of ${PACKAGE_NAME} include"
    NO_DEFAULT_PATH
)
set(${PACKAGE_NAME}_INCLUDE_DIR ${${PACKAGE_NAME}_INCLUDE_DIR} CACHE STRING "")
mark_as_advanced(${PACKAGE_NAME}_INCLUDE_DIR)
# message("DEBUG ${PACKAGE_NAME}_INCLUDE_DIR ${${PACKAGE_NAME}_INCLUDE_DIR}")

# # find libraries
# set(_lib UsoroWindow)
# set(_lib_suffixes Lib)
# find_library(
#     ${PACKAGE_NAME}_LIBRARY
#     NAMES ${_lib}${_lib_suffixes}
#     PATHS ${${PACKAGE_NAME}_LIBRARY_DIR}
#     DOC "Location of ${PACKAGE_NAME} library"
#     NO_DEFAULT_PATH
# )
# mark_as_advanced(${PACKAGE_NAME}_LIBRARY)
# select_library_configurations(${PACKAGE_NAME}_${_lib})

# generate cmake variables
find_package_handle_standard_args(
    ${PACKAGE_NAME}
    # REQUIRED_VARS ${PACKAGE_NAME}_LIBRARY ${PACKAGE_NAME}_INCLUDE_DIR
    REQUIRED_VARS ${PACKAGE_NAME}_INCLUDE_DIR
    VERSION_VAR ${PACKAGE_NAME}_VERSION
)

# header only package has no library
set(${PACKAGE_NAME}_LIBRARY "NONE" CACHE STRING "")

# set found dirs
if(${PACKAGE_NAME}_FOUND)
    set(${PACKAGE_NAME}_INCLUDE_DIRS ${${PACKAGE_NAME}_INCLUDE_DIR})
    set(${PACKAGE_NAME}_LIBRARIES ${${PACKAGE_NAME}_LIBRARY})
    # # setup target package
    # set(GTEST_LIBRARY_TYPE UNKNOWN)
    # set(_target_name Usoro)
    # set(_lib_name Usoro)
    # set(_target ${_target_name}::${_lib_name})
    # if(NOT TARGET ${_target})
    #     add_library(${_target} ${GTEST_LIBRARY_TYPE} IMPORTED)
    #     if(${PACKAGE_NAME}_INCLUDE_DIR)
    #         # message("-- DEBUG ${PACKAGE_NAME}_INCLUDE_DIR ${${PACKAGE_NAME}_INCLUDE_DIR}")
    #         set_target_properties(${_target} PROPERTIES
    #             INTERFACE_INCLUDE_DIRECTORIES "${${PACKAGE_NAME}_INCLUDE_DIR}")
    #     endif()
    #     set(_config_suffix "")
    #     set_target_properties(
    #         ${_target} PROPERTIES
    #         IMPORTED_LOCATION${_config_suffix} "${${PACKAGE_NAME}_LIBRARY}"
    #     )
    # endif()
endif()