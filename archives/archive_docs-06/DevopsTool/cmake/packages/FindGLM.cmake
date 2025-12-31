# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Find package GLM
# @note : N/A
#-----------------------------------------------------------
include(FindPackageHandleStandardArgs)
include(SelectLibraryConfigurations)

# Set package cmake attributes
# set paths
set(PACKAGE_NAME GLM)
string(TOUPPER ${PACKAGE_NAME} UPACKAGE_NAME)
set(${PACKAGE_NAME}_DIR ${${UPACKAGE_NAME}_ROOT})
set(${PACKAGE_NAME}_LIBRARY_DIR ${${PACKAGE_NAME}_DIR}/lib)
set(${PACKAGE_NAME}_INCLUDE_DIR ${${PACKAGE_NAME}_DIR}/include)

# find libraries
# N/A

# find includes
if (WIN32)
    # Find include files
    find_path(
        ${PACKAGE_NAME}_INCLUDE_DIR
        NAMES glm/glm.hpp
        PATHS
        $ENV{PROGRAMFILES}/include
        ${${PACKAGE_NAME}_DIR}/include
        DOC "The directory where glm/glm.hpp resides")
else()
    # Find include files
    find_path(
        ${PACKAGE_NAME}_INCLUDE_DIR
        NAMES glm/glm.hpp
        PATHS
        /usr/include
        /usr/local/include
        /sw/include
        /opt/local/include
        ${${PACKAGE_NAME}_DIR}/include
        DOC "The directory where glm/glm.hpp resides")
endif()

# generate cmake variables
# Handle REQUIRD argument, define *_FOUND variable
find_package_handle_standard_args(
    ${PACKAGE_NAME}
    REQUIRED_VARS ${PACKAGE_NAME}_INCLUDE_DIR
    VERSION_VAR ${PACKAGE_NAME}_VERSION
)

# set found dirs
# Define GLM_INCLUDE_DIRS
if(${PACKAGE_NAME}_FOUND)
    set(${PACKAGE_NAME}_INCLUDE_DIRS ${${PACKAGE_NAME}_INCLUDE_DIR})
    set(${PACKAGE_NAME}_LIBRARIES ${${PACKAGE_NAME}_LIBRARY})
endif()

# Hide some variables
mark_as_advanced(GLM_INCLUDE_DIR)
