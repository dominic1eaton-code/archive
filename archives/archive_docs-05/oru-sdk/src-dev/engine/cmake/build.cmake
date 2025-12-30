# @license
# @brief


macro(configure_environment)
    # global
    configure_global_environment()

    # project options
    options(BUILD_SHARED_LIBS "build using shared libraries" ON)
    options(BUILD_TESTS "build  unit tests" OFF)
    options(BUILD_VERBOSE "build with verbose logging" OFF)
endmacro()