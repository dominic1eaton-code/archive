#-----------------------------------------------------------
# @header DEFAULT
# @brief
# @note
#-----------------------------------------------------------
cmake_minimum_required(VERSION 3.18)

#-----------------------------------------------------------
# @brief Setup project dependencies
# @note
#-----------------------------------------------------------
macro(setup_dependencies)
    set(_versions_file ${CMAKE_BINARY_DIR0}/${VERSION_INFO_FILE})
    # file(WRITE "${_versions_file}" "")

    configure_package(Vulkan 1.3.296.0 "." Vulkan VULKAN_SDK)
    configure_package(STB 1.0.0 "." STB STB_DIR)
    configure_package(glm 1.0.2 "." glm glm_DIR)
    configure_package(Eigen3 3.3 "." Eigen Eigen3_DIR)
    # configure_package(assimp 5.4.3 "." assimp assimp_DIR)
    # configure_package(CXXOpts 5.3.0 "." CXXOpts CXXOpts_DIR)
endmacro()
