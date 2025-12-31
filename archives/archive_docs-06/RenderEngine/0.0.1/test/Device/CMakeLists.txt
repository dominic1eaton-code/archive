# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: project unit test file
# @note : N/A
#-----------------------------------------------------------
project(DeviceTest)

# get unit test code source to be tested
global_unit_test_library_source(
    Devices
    Graphics
)

# unit test code
set(UNIT_TEST_SOURCE
    DeviceTest.cpp
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
message("LIBRARIES_UNDER_TEST ${LIBRARIES_UNDER_TEST}")
global_unit_test_link_libraries(
    LIBS_UNDER_TEST ${LIBRARIES_UNDER_TEST}
)

# install test targets
target_compile_features(${PROJECT_NAME} PUBLIC ${CPP_STD_VERSION})
global_install(
    ${PROJECT_NAME}
)