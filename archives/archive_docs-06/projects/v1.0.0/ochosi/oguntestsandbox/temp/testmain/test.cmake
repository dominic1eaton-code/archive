



# package attributes
# set(GTest       1.15.2      ".")
# set(VulkanSDK   1.3.296.0   ".")
# set(STB         1.0.0       ".")
# set(GLM         1.0.2       ".")
# set(Eigen3      3.3         ".")z


    
# set(ENV{VK_LAYER_PATH} "${PROJECT_MOUNT}/global/VulkanSDK/1.3.296.0/Bin")
# set(ENV{VULKAN_SDK} "${PROJECT_MOUNT}/global/VulkanSDK/1.3.296.0")
# find_package(Vulkan REQUIRED)
# target_link_libraries(${PROJECT_NAME} Vulkan::Vulkan)
# target_include_directories(${PROJECT_NAME} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/${_src})
# set(ENV{Eigen3_DIR} "${PROJECT_MOUNT}/global/Eigen/3.4.0")
# find_package(Eigen3 3.3 REQUIRED NO_MODULE)
# target_link_libraries(${PROJECT_NAME}  Eigen3::Eigen)
# set(ENV{glm_DIR} "${PROJECT_MOUNT}/global/GLM/1.0.2")
# find_package(glm CONFIG REQUIRED)
# target_link_libraries(${PROJECT_NAME} glm::glm)
# set(STB_PATH "${PROJECT_MOUNT}/global/STB/1.0.0")
# target_include_directories(${PROJECT_NAME} PUBLIC ${STB_PATH})



# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief
# @description
# @note
#-----------------------------------------------------------
macro(common_find_package PACKAGE)
    # input args 
    set(_options "")
    set(_oneValueArgs NO_LIB)
    # set(_multiValueArgs )
    cmake_parse_arguments(
        ARGS
        "${_options}"
        "${_oneValueArgs}"
        "${_multiValueArgs}"
        ${ARGN}
    )

    find_package(${PACKAGE} ${ARGN} REQUIRED)
    add_definitions(${${PACKAGE}_DEFINITIONS})
    # target_link_libraries(${PROJECT_NAME} ${${PACKAGE}_LIBRARIES})
    if(NOT "${${PACKAGE}_LIBRARY}" STREQUAL "NONE")
        target_link_libraries(${PROJECT_NAME} ${PACKAGE}::${${PACKAGE}_LIBRARY_NAME})
    endif()
    target_include_directories(${PROJECT_NAME} PUBLIC ${${PACKAGE}_INCLUDE_DIR})
endmacro()





target_include_directories(
    ${PROJECT_NAME} PUBLIC 
    ${PROJECT_NAME}/Modules
    ${PROJECT_NAME}/Kernel)

    