# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: project unit test file
# @note : N/A
#-----------------------------------------------------------
project(RendererMainTest)

# list source files
list(
    APPEND PROJECT_SOURCE
    triangleApplicationTest.cpp
)

# list headers
list(
    APPEND PROJECT_HEADERS
    triangleApplicationTest.h
)

# # get test data
# set(
#     UNIT_TEST_DATA
# )

# # get unit test code source to be tested
# global_unit_test_library_source(
#     Graphics
# )

# # create test executable
# global_unit_test(
#     ${PROJECT_NAME}
#     UNIT_TEST_CODE_SRC ${UNIT_TEST_CODE_SOURCE}
#     UNIT_TEST_SRC      ${PROJECT_SOURCE}
#     UNIT_TEST_DATA_SRC ${UNIT_TEST_DATA}
# )

# # link test libraries 
# global_unit_test_link_libraries(
#     LIBS_UNDER_TEST ${LIBRARIES_UNDER_TEST}
# )

# # install test targets
# target_compile_features(${PROJECT_NAME} PUBLIC ${CPP_STD_VERSION})
# global_install(
#     ${PROJECT_NAME}
# )

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create library
add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)

# link dependencies
global_target_link_libraries(
    Graphics
)

# install test targets
target_compile_features(${PROJECT_NAME} PUBLIC ${CPP_STD_VERSION})
global_install(
    ${PROJECT_NAME}
)