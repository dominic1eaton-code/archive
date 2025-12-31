# @copyright
# @brief: Setup Wrap find package functionality
# @note : N/A
cmake_minimum_required(VERSION 3.18)

#-----------------------------------------------------------
# @brief: Setup unit test
# @note : N/A
# @usage: include(globalSetupTest)
#         global_setup_unit_test(PACKAGE)
#-----------------------------------------------------------
macro(global_setup_unit_test)
    # find unit test tool
    # set(GTEST_ROOT "C:/global/GTest/1.15.2" CACHE PATH "GTest path")
    if (WIN32)
        set(GTEST_ROOT "C:/global/GTest/googletest/install/win32" CACHE PATH "gtest path")
    elseif(UNIX)
        set(GTEST_ROOT "C:/global/GTest/googletest/install/unix" CACHE PATH "gtest path")
    endif()
    find_package(GTest REQUIRED)

    # Cmake utility that allows tests to be generated
    # from add_test() function
    enable_testing()

    # install unit test tool windows dlls
    if (BUILD_VERBOSE)
        message("DEBUG install ${GTEST_ROOT}/bin ")
    endif()
    install(
        DIRECTORY   "${GTEST_ROOT}/bin/"
        # DESTINATION "${CMAKE_HOME_DIRECTORY}/${CMAKE_INSTALL_PREFIX}/bin/"
        DESTINATION "${PROJECT_INSTALLATION_PATH}/bin"
        COMPONENT   UNIT_TEST_TOOL_FILES
    )
endmacro()

#-----------------------------------------------------------
# @brief: Setup unit test
# @note : N/A
# @usage: include(globalSetupTest)
#         global_check_unit_test()
#-----------------------------------------------------------
macro(global_check_unit_test)
    set(oneValueArgs DISABLE_OVERRIDE)
    cmake_parse_arguments(
        ARG                 # Prefix of output variables
        "${options}"        # Boolean args
        "${oneValueArgs}"   # One valued args (i.e. key/value)
        "${multiValueArgs}" # List based arguments
        ${ARGN}             # Input arguments
    )

    # If disabled override string provided
    if (ARG_DISABLE_OVERRIDE)
        set(UNIT_TEST_DISABLE_OVERRIDE "${UNIT_TESTS_DISABLED};${PROJECT_NAME} : ${DISABLE_OVERRIDE}" CACHE INTERNAL "" FORCE)
    # elseif(${ENABLE_UNIT_TEST})
    else()
        if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/test/CMakeLists.txt)
            if(UNIT_TESTS)
                list(FIND UNIT_TESTS "${CMAKE_CURRENT_SOURCE_DIR}/test" _index)
            else()
                set(_index -1)
            endif()
            if(NOT ${_index} GREATER -1)
                message(" UNIT_TESTS UNIT_TESTS")
                set(UNIT_TESTS "${UNIT_TESTS};${CMAKE_CURRENT_SOURCE_DIR}/test" CACHE INTERNAL "" FORCE)
                set(UNIT_TESTS_ENABLED "${UNIT_TESTS_ENABLED};${PROJECT_NAME}" CACHE INTERNAL "" FORCE)
            endif()
        else()
            if(UNIT_TESTS_DISABLED)
                list(FIND UNIT_TESTS_DISABLED "${PROJECT_NAME}" _index)
            else()
                set(_index -1)
            endif()
            if(NOT ${_index} GREATER -1)
                set(UNIT_TESTS_DISABLED "${UNIT_TESTS_DISABLED};${PROJECT_NAME}" CACHE INTERNAL "" FORCE)
            endif()
        endif()
    endif()
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

    if(BUILD_VERBOSE)
        message("DEBUG ARG_UNIT_TEST_CODE_SRC ${ARG_UNIT_TEST_CODE_SRC}")
        message("DEBUG ARG_UNIT_TEST_SRC ${ARG_UNIT_TEST_SRC}")
        message("create unit test exe  UNIT_TEST ${UNIT_TEST}")
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
    if(BUILD_VERBOSE)
        message("DEBUG GTEST_INCLUDE_DIR ${GTEST_INCLUDE_DIR}")
        message("DEBUG GTEST_LIBRARY ${GTEST_LIBRARY}")
        message("DEBUG GTEST_MAIN_LIBRARY ${GTEST_MAIN_LIBRARY}")
        message("DEBUG UNIT_TEST ${UNIT_TEST}")
        message("DEBUG GTEST_LIBRARIES ${GTEST_LIBRARIES}")
        message("DEBUG GTEST_MAIN_LIBRARIES ${GTEST_MAIN_LIBRARIES}")
        message("DEBUG UNIT_TEST ${UNIT_TEST}")
    endif()
    include(GoogleTest)
    target_include_directories(
        ${UNIT_TEST}
        PUBLIC ${GTEST_INCLUDE_DIR}
    )
    target_link_libraries(
        ${UNIT_TEST}
        PUBLIC ${GTEST_LIBRARY} ${GTEST_MAIN_LIBRARY}
        # PRIVATE ${GTEST_LIBRARIES} ${GTEST_MAIN_LIBRARIES}
    )

    # add unit test tool dlls
    # file(COPY "${GTEST_ROOT}/bin/" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/")
    if(BUILD_VERBOSE)
        message("DEBUG global_unit_test GTEST_ROOT ${GTEST_ROOT}")
        message("DEBUG CMAKE_CURRENT_BINARY_DIR ${CMAKE_CURRENT_BINARY_DIR}")
        message("DEBUG CMAKE_BINARY_DIR ${CMAKE_BINARY_DIR}")
        message("DEBUG GTEST_ROOT bin ${GTEST_ROOT}/bin/")
        message("DEBUG MAKE_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/Release")
    endif()
    
    if (WIN32)
        # copy Gtest shared libraries to directory of test executable
        # @todo include unit test libraries based on configuration type
        file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/Release")
        if(EXISTS ${CMAKE_CURRENT_BINARY_DIR}/Release)
            file(COPY "${GTEST_ROOT}/bin/" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/Release")
        endif()

        file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/Debug")
        if(EXISTS ${CMAKE_CURRENT_BINARY_DIR}/Debug)
            file(COPY "${GTEST_ROOT}/bin/" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/Release")
        endif()
    endif()

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

    # add test target if CTest is enabled
    if(NOT ${ARG_NO_CTEST})
        if(BUILD_VERBOSE)
            message("DEBUG global_unit_test ADD UNIT_TEST ${UNIT_TEST}")
        endif()
        add_test(
            NAME ${UNIT_TEST}
            COMMAND ${UNIT_TEST}
            ${_test_flags}
        )
        gtest_discover_tests(${UNIT_TEST})
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

    if(BUILD_VERBOSE)
        message("DEBUG LIBRARIES_UNDER_TEST  ${LIBRARIES_UNDER_TEST}")
        message("DEBUG ARG_LIBS_UNDER_TEST  ${ARG_LIBS_UNDER_TEST}")
    endif()
    if(NOT ARG_LIBS_UNDER_TEST)
        message(FATAL_ERROR "No library under test specified")
    endif()
    
    # get source project link libraries
    foreach(_project IN ITEMS ${ARG_LIBS_UNDER_TEST})
        get_target_property(_unit_test_library ${_project} INTERFACE_LINK_LIBRARIES)
        get_target_property(_unit_test_include ${_project} INCLUDE_DIRECTORIES)
    
        list(APPEND _unit_test_libraries ${_unit_test_library})
        list(APPEND _unit_test_includes ${_unit_test_include})
        if(BUILD_VERBOSE)
            message("DEBUG _project  ${_project}")
            message("DEBUG _unit_test_library  ${_unit_test_library}")
            message("DEBUG _unit_test_include  ${_unit_test_include}")
        endif()
    endforeach()

    list(FILTER _unit_test_libraries EXCLUDE REGEX ".*NOTFOUND.*")
    list(FILTER _unit_test_includes EXCLUDE REGEX ".*NOTFOUND.*")
    list(REMOVE_DUPLICATES _unit_test_libraries)
    list(REMOVE_DUPLICATES _unit_test_includes)

    # if(BUILD_VERBOSE)
        message("DEBUG _unit_test_libraries  ${_unit_test_libraries}")
        message("DEBUG _unit_test_includes  ${_unit_test_includes}")
    # endif()
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
# @brief: Gather source files of library being tested
# @note : N/a
# @usage: include(globalSetupTest)
#         global_unit_test_library_source()
#-----------------------------------------------------------
macro(global_unit_test_library_source)
    if(BUILD_VERBOSE)
        message("DEBUG global_unit_test_library_source LIBRARIES_UNDER_TEST ${ARGN}")
    endif()
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

        if(BUILD_VERBOSE)
            message("DEBUG global_unit_test_library_source project ${_project}")
            message("DEBUG global_unit_test_library_source LIBRARY_UNDER_TEST_SOURCE ${LIBRARY_UNDER_TEST_SOURCE}")
            message("DEBUG global_unit_test_library_source UNIT_TEST_CODE_SOURCE ${LIBRARY_UNDER_TEST_SOURCE}")
            message("DEBUG global_unit_test_library_source PROJECT_INCLUDES ${PROJECT_INCLUDES}")
        endif()
    endforeach()
    set(LIBRARIES_UNDER_TEST ${ARGN})
    if(BUILD_VERBOSE)
        message("DEBUG global_unit_test_library_source LIBRARIES_UNDER_TEST ${LIBRARIES_UNDER_TEST}")
    endif()
endmacro()

#-----------------------------------------------------------
# @brief: Gather unit test source files
# @note : N/a
# @usage: include(globalSetupTest)
#         global_unit_test_library_source()
#-----------------------------------------------------------
macro(global_check_tests_exist)
    message("checking tests exist for project")
    message("current dir : ${CMAKE_CURRENT_SOURCE_DIR}")
    if(IS_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/test")
        add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/test")
    else()
        # Directory does not exist, handle accordingly
        message(WARNING "Directory does not exist!")
    endif()
endmacro()

#-----------------------------------------------------------
# @brief: Add unit tests if any where detected in project
#         targets
# @note : N/a
# @usage: include(globalSetupTest)
#         global_unit_test_library_source()
#-----------------------------------------------------------
macro(global_add_unit_tests)
    message("Unit Tests Enabled: ")
    # about 80 cols in given terminal, with 80 / 3 ~= 26
    set(_MAX_CHARACTERS_PER_COLUMN 26)
    set(_MAX_COLUMNS 3)

    # print unit tests names column wise
    set(_index 0)

    set(_char_per_column ${_MAX_CHARACTERS_PER_COLUMN})
    set(_num_columns ${_MAX_COLUMNS})
    set(_unit_tests_enabled ${UNIT_TESTS_ENABLED})
    list(SORT _unit_tests_enabled)
    foreach(_name ${UNIT_TESTS_ENABLED})
        string(LENGTH ${_name} _len)
        math(EXPR _count "${_char_per_column} - ${_len}")
        if(${_count} GREATER 0)
            string(REPEAT " " ${_count} _padding)
            set(_result "${result}${_name}${_padding}")
        else()
            set(_result "${result}${_name} ")
        endif()

        math(EXPR _index "${index} + 1")
        if (${index} EQUAL ${num_columns})
            set(_index 0)
            message(STATUS ${_result})
            unset(_result)
        endif()
    endforeach()
    if(_result)
        message(STATUS ${_result})
        unset(_result)
    endif()
    
    # add unit test to project
    if(${BUILD_TESTS})
        foreach(_unit_test ${UNIT_TESTS})
            add_subdirectory(${_unit_test})
        endforeach()
    endif()
    
    # folders with explicit disabled unit tests
    if (UNIT_TEST_DISABLE_OVERRIDE)
        message(STATUS "Unit Test DISABLED: ")
        set(_unit_tests_disabled ${UNIT_TEST_DISABLE_OVERRIDE})
        list(SORT _unit_tests_disabled)
        foreach(_unit_test_name ${_unit_tests_disabled})
            message(STATUS "x ${_unit_test_name}")
        endforeach()
    endif()

    # folders with no/missing unit tests
    if (UNIT_TESTS_DISABLED)
        message(STATUS "Unit Test MISSING: ")
        set(_unit_tests_missing ${UNIT_TESTS_DISABLED})
        set(_index 0)
        list(SORT _unit_tests_missing)
        foreach(_name ${_unit_tests_missing})
            string(LENGTH ${_name} _len)
            math(EXPR _count "${_MAX_CHARACTERS_PER_COLUMN} - ${_len}")
            if(${_count} GREATER 0)
                string(REPEAT " " ${_count} _padding)
                set(_result "${_result}${_name}${_padding}")
            else()
                set(_result "${_result}${_name}")
            endif()
            math(EXPR _index "${_index} + 1")
            # if (${_index} EQUAL ${_MAX_COLUMNS})
            set(_index 0)
            message(STATUS ${_result})
            unset(_result)
            # endif()
        endforeach()
    endif()
    message("Unit Test setup complete")
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
    if(BUILD_VERBOSE)
        message("DEBUG global_get_project_sources _source_files ${_source_files}")
        message("DEBUG global_get_project_sources _source_dir ${_source_dir}")
    endif()

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