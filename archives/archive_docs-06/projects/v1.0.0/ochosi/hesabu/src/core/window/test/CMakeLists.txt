# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: project unit test file
# @note : N/A
#-----------------------------------------------------------
project(HesabuWindowTest)

# get unit test code source to be tested
global_unit_test_library_source(
    HesabuWindow
)

# unit test code
set(UNIT_TEST_SOURCE
    testwindow.cpp
    # testwindowfixture.h
)

# get test data
set(
    UNIT_TEST_DATA
)

# create test executable
global_unit_test(
    ${PROJECT_NAME}
    UNIT_TEST_CODE_SRC  ${UNIT_TEST_CODE_SOURCE}
    UNIT_TEST_SRC       ${UNIT_TEST_SOURCE}
    UNIT_TEST_DATA_SRC  ${UNIT_TEST_DATA}
)

# link test libraries
global_unit_test_link_libraries(
    LIBS_UNDER_TEST ${LIBRARIES_UNDER_TEST}
)
