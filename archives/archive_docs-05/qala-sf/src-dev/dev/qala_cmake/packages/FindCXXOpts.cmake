# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Find package LoggerCPP TEST LOGGER LIBRARY
# @note : N/A
#-----------------------------------------------------------
include(FindPackageHandleStandardArgs)
include(SelectLibraryConfigurations)

# Set package cmake attributes
# set paths
set(PACKAGE_NAME CXXOpts)
string(TOUPPER ${PACKAGE_NAME} UPACKAGE_NAME)
set(${PACKAGE_NAME}_DIR ${${UPACKAGE_NAME}_PATH})
set(${PACKAGE_NAME}_INCLUDE_DIR ${${PACKAGE_NAME}_PATH}/include)

# find includes
set(_include cxxopts.hpp)
find_path(
    ${PACKAGE_NAME}_INCLUDE_DIR
    NAMES ${_include}
    PATHS ${${PACKAGE_NAME}_INCLUDE_DIR}
    DOC "Location of ${PACKAGE_NAME} include"
    NO_DEFAULT_PATH
)
set(${PACKAGE_NAME}_INCLUDE_DIR ${${PACKAGE_NAME}_INCLUDE_DIR} CACHE STRING "")
mark_as_advanced(${PACKAGE_NAME}_INCLUDE_DIR)

# generate cmake variables
find_package_handle_standard_args(
    ${PACKAGE_NAME}
    REQUIRED_VARS ${PACKAGE_NAME}_INCLUDE_DIR
    VERSION_VAR ${PACKAGE_NAME}_VERSION
)
 
# header only package has no library
set(${PACKAGE_NAME}_LIBRARY "NONE" CACHE STRING "")

# set found dirs
if(${PACKAGE_NAME}_FOUND)
    set(${PACKAGE_NAME}_INCLUDE_DIRS ${${PACKAGE_NAME}_INCLUDE_DIR})
    set(${PACKAGE_NAME}_LIBRARIES ${${PACKAGE_NAME}_LIBRARY})
endif()
