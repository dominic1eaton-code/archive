# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Common dependencies setup for project
# @note : N/A
#-----------------------------------------------------------
include(globalConfigurePackage)

#-----------------------------------------------------------
# @brief: Setup dependencies for project
# @note : N/A
#-----------------------------------------------------------
macro(project_setup_dependencies)
    # configure_package(GTest 1.12.2 "")
    set(GTEST_ROOT "F:/ots/gtest/1.12.2")
    find_package(GTest REQUIRED)

    set(VULKAN_ROOT "F:/ots/VulkanSDK/1.3.204.0")
    find_package(Vulkan REQUIRED)
    
    set(SDL2_ROOT "F:/ots/SDL2/2.0.22")
    find_package(SDL2 REQUIRED)
    message("SDL2_INCLUDE_DIRS ${SDL2_INCLUDE_DIRS}")
endmacro()
