# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Setup Wrap find package functionality
# @note : N/A
#-----------------------------------------------------------

#-----------------------------------------------------------
# @brief: Setup unit test
# @note : N/A
# @usage: include(globalSetupTest)
#         global_setup_unit_test(PACKAGE)
#-----------------------------------------------------------
macro(global_setup_unit_test)
    # find unit test tool
    set(GTEST_ROOT "F:/ots/gtest/1.12.2")
    find_package(GTest REQUIRED)

    # Cmake utility that allows tests to be generated
    # from add_test() function
    enable_testing()

    # install unit test tool windows dlls
    message("install ${GTEST_ROOT}/bin ")
    install(
        DIRECTORY   "${GTEST_ROOT}/bin/"
        DESTINATION "${CMAKE_HOME_DIRECTORY}/${CMAKE_INSTALL_PREFIX}/bin/"
        COMPONENT   UNIT_TEST_TOOL_FILES
    )
endmacro()

#-----------------------------------------------------------
# @brief: Generate individual unit test suite
# @note : N/a
# @usage: include(globalSetupTest)
#         global_find_package(PACKAGE)
#-----------------------------------------------------------
macro(global_unit_test UNIT_TEST)
    # input args
    set(_options NO_CTEST NO_STUBS COPY_TEST_DATA)
    set(_multiValueArgs UNIT_TEST_CODE_SRC UNIT_TEST_SRC UNIT_TEST_DATA_SRC TEST_FLAGS)
    cmake_parse_arguments(
        ARG
        "${_options}"
        "${_oneValueArgs}"
        "${_multiValueArgs}"
        ${ARGN}
    )

    # ensure check if unit test source files were passed in
    if(NOT ARG_UNIT_TEST_SRC)
        message(FATAL_ERROR "-- global_unit_test: ${UNIT_TEST} requires unit test source files")
    endif()

    # generate executable
    message("create unit test exe")
    add_executable(
        ${UNIT_TEST}
        ${ARG_UNIT_TEST_CODE_SRC}
        ${ARG_UNIT_TEST_SRC}
    )

    # link test tool library
    # include_directories(${GTEST_INCLUDE_DIR})
    # target_link_libraries(${UNIT_TEST} PRIVATE GTest::gtest GTest::gtest_main)
    include(GoogleTest)
    target_include_directories(
        ${UNIT_TEST}
        PUBLIC ${GTEST_INCLUDE_DIR}
    )
    target_link_libraries(
        ${UNIT_TEST}
        PRIVATE ${GTEST_LIBRARIES} ${GTEST_MAIN_LIBRARIES}
    )

    # add unit test tool dlls
    # file(COPY "${GTEST_ROOT}/bin/" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/")
    file(COPY "${GTEST_ROOT}/bin/" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/")

    # generate test
    set(_test_flags 
        --log_format=HRF
        --log_sink=stdout
        --log_level=message
        --report_format=HRF
        --report_level=detailed
        --report_sink=report.txt
        --rerun-failed
        --output-on-failure
    )
    list(APPEND _test_flags ${ARG_TEST_FLAGS})

    # add test target if CTEST is enabled
    if(NOT ${ARG_NO_CTEST})
        add_test(
            ${UNIT_TEST}
            ${UNIT_TEST}
            ${_test_flags}
        )
    endif()
endmacro()

#-----------------------------------------------------------
# @brief: Link unit test libraries
# @note : N/a
# @usage: include(globalSetupTest)
#         global_unit_test_link_libraries()
#-----------------------------------------------------------
macro(global_unit_test_link_libraries)
    # input args 
    set(_options NO_DEFAULT_SYSTEM_LIBS)
    set(_multiValueArgs LIBS_UNDER_TEST)
    cmake_parse_arguments(
        ARG
        "${_options}"
        "${_oneValueArgs}"
        "${_multiValueArgs}"
        ${ARGN}
    )

    if(NOT ARG_LIBS_UNDER_TEST)
        message(FATAL_ERROR "No library under test specified")
    endif()
    
    # get source project link libraries
    foreach(_project IN ITEMS ${ARG_LIBS_UNDER_TEST})
        get_target_property(_unit_test_library ${_project} INTERFACE_LINK_LIBRARIES)
        get_target_property(_unit_test_include ${_project} INCLUDE_DIRECTORIES)
    
        list(APPEND _unit_test_libraries ${_unit_test_library})
        list(APPEND _unit_test_includes ${_unit_test_include})
    endforeach()

    list(FILTER _unit_test_libraries EXCLUDE REGEX ".*NOTFOUND.*")
    list(FILTER _unit_test_includes EXCLUDE REGEX ".*NOTFOUND.*")
    list(REMOVE_DUPLICATES _unit_test_libraries)
    list(REMOVE_DUPLICATES _unit_test_includes)

    # include and link libraries
    target_include_directories(
        ${PROJECT_NAME}
        PUBLIC ${_unit_test_includes}
    )
    target_link_libraries(
        ${PROJECT_NAME}
        PRIVATE ${_unit_test_libraries}
    )
endmacro()

#-----------------------------------------------------------
# @brief: Gather unit test source files
# @note : N/a
# @usage: include(globalSetupTest)
#         global_unit_test_library_source()
#-----------------------------------------------------------
macro(global_unit_test_library_source)
    foreach(_project IN ITEMS ${ARGN})
        # get library under test source 
        global_get_project_sources(LIBRARY_UNDER_TEST_SOURCE ${_project})

        # define library under test 
        list(APPEND UNIT_TEST_CODE_SOURCE "${LIBRARY_UNDER_TEST_SOURCE}")

        # get library under test includes 
        get_target_property(PROJECT_INCLUDES ${_project} INCLUDE_DIRECTORIES)
        
        if(PROJECT_INCLUDES)
            include_directories(${PROJECT_INCLUDES})
        endif()
    endforeach()
    set(LIBRARIES_UNDER_TEST ${ARGN})
endmacro()

#-----------------------------------------------------------
# @brief: Gather unit test source files
# @note : N/a
# @usage: include(globalSetupTest)
#         global_unit_test_library_source()
#-----------------------------------------------------------
macro(global_check_tests_exist)
    message("checking tests exist for project")
endmacro()

#-----------------------------------------------------------
# @brief: Add unit tests if any where detected in project
#         targets
# @note : N/a
# @usage: include(globalSetupTest)
#         global_unit_test_library_source()
#-----------------------------------------------------------
macro(global_add_unit_tests)
    add_subdirectory("${PROJECT_TEST_PATH}")
endmacro()

#-----------------------------------------------------------
# @brief: Gather unit test source files
# @note : N/a
# @usage: include(globalSetupTest)
#         global_get_project_sources()
#-----------------------------------------------------------
function(global_get_project_sources VARIABLE PROJECT_NAME)
    get_property(_source_files TARGET ${PROJECT_NAME} PROPERTY SOURCES)
    get_property(_source_dir TARGET ${PROJECT_NAME} PROPERTY SOURCE_DIR)
    if(_source_files)
        # remove header files 
        # list(FILTER _source_files INCLUDE REGEX ".*[.]c[p]*")
        # convert paths to absolute
        foreach(_file ${_source_files})
            if(IS_ABSOLUTE "${_file}")
                list(APPEND _abs_source_files "${_file}")
            else()
                list(APPEND _abs_source_files "${_source_dir}/${_file}")
            endif()
        endforeach()
        set(${VARIABLE} ${_abs_source_files} PARENT_SCOPE)
    else()
        message(FATAL_ERROR "No source files found for ${PROJECT_NAME}")
    endif()
endfunction()
