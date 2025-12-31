# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Setup common build environment
# @note : N/A
# Debugging references:
#   https://stackoverflow.com/questions/28178978/how-to-generate-pdb-files-for-release-build-with-cmake-flags
#   https://stackoverflow.com/questions/54856175/vscode-c-debugging-code-built-with-cl-exe-and-link-exe-debugger-doesnt-at
#   https://stackoverflow.com/questions/46237620/how-to-install-debugging-tools-with-visual-studio-2017-installer
#   https://stackoverflow.com/questions/63075138/where-is-the-c-debugger-executable-located-in-visual-studio-2015
#   https://blog.futrime.com/en/p/compiling-c/c-programs-in-vscode-with-msvc/
#-----------------------------------------------------------
include(globalPackageManager)

#-----------------------------------------------------------
# @brief: Setup common build environment variables, defines
#         settings, compiler, linker options etc...
# @note : Recommended to call this macro before all others 
#         when included in a project
# @usage: include(globalSetupBuildEnvironment)
#         global_setup_build_environment()
#-----------------------------------------------------------
macro(global_setup_build_environment)
    # default project cmake build type
    set(PROJECT_DEFAULT_CMAKE_BUILD_TYPE Debug)

    # set default build type if not defined explicitly. 
    # Targetted to be used by single (namely, UNIX) generators 
    if(UNIX)
        if("${CMAKE_BUILD_TYPE}" STREQUAL "")
            set(CMAKE_BUILD_TYPE
                ${PROJECT_DEFAULT_CMAKE_BUILD_TYPE}
                CACHE STRING
                "Choose type of cmake build: Debug Release RelWithDebInfo")
        endif()
    endif()

    # Set windows MSVC compiler flags
    if(WIN32)
        # Disable use of MFC by VS
        set(CMAKE_MFC_FLAG 0)

        # Enable parallel builds
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /MP")

        # Enable string pooling to eliminate duplicate strings
        # https://learn.microsoft.com/en-us/cpp/build/reference/gf-eliminate-duplicate-strings?view=msvc-170
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /GF")

        # Increase warning sensitivity
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /W3")

        # Suppress VS compiler startup banner
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /nologo")

        # generate pdb files to allow debuggging
        # https://stackoverflow.com/questions/28178978/how-to-generate-pdb-files-for-release-build-with-cmake-flags
        # https://stackoverflow.com/questions/54856175/vscode-c-debugging-code-built-with-cl-exe-and-link-exe-debugger-doesnt-at
        # https://stackoverflow.com/questions/46237620/how-to-install-debugging-tools-with-visual-studio-2017-installer
        set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} /Zi" CACHE STRING "" FORCE)
        set(CMAKE_SHARED_LINKER_FLAGS_RELEASE "${CMAKE_SHARED_LINKER_FLAGS_RELEASE} /DEBUG /OPT:REF /OPT:ICF" CACHE STRING "" FORCE)
    endif()

    # Enable ccache by default
    set(CMAKE_CXX_COMPILER_LAUNCHER ccache CACHE STRING
       "Enable ccache by default to improve subsequent build performance")

    # Setup build environment utiltities
    setup_package_manager()
endmacro()