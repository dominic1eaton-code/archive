# @header 
# @copyright
# @brief
# @note
cmake_minimum_required(VERSION 3.18)
project(TestKernel0)

set(ogun Ogun)
set(core Ogun/Core)
set(buffer Ogun/Buffer)
set(sync Ogun/Sync)
set(hesabu Hesabu)

# source files
list(
    APPEND PROJECT_SOURCES

    main.cpp

    ${core}/VInstance.cpp
    ${core}/VDevice.cpp
    ${core}/VSurface.cpp
    ${core}/VShader.cpp
    ${core}/VRenderPass.cpp
    ${core}/VPipeline.cpp
    ${core}/VDescriptorLayout.cpp
    # ${core}/VImage.cpp
    # ${core}/VCommand.cpp
    ${core}/VShaderManager.cpp
    ${core}/VSyncManager.cpp

    ${buffer}/VFrameBuffer.cpp
    ${buffer}/VSwapchain.cpp
    # ${buffer}/VCommandBuffer.cpp
    
    ${sync}/VFence.cpp
    ${sync}/VSemaphore.cpp

    ${hesabu}/Window/HWindow.cpp

)

# headers files
list(
    APPEND PROJECT_HEADERS
    
    vulkan_model.h
    vulkan_scene.h
    vulkan_shader.h

    ${core}/VObject.h
    ${core}/VDevice.h
    ${core}/VSurface.h
    ${core}/VShader.h
    ${core}/VFile.h
    ${core}/VRenderPass.h
    ${core}/VPipeline.h
    ${core}/Vertex.h
    ${core}/VDescriptorLayout.h
    ${core}/VConstants.h
    # ${core}/VImage.h
    # ${core}/VCommand.h
    ${core}/VShaderManager.h
    ${core}/VSyncManager.h

    ${buffer}/VFrameBuffer.h
    ${buffer}/VSwapchain.h
    # ${buffer}/VCommandBuffer.h
    
    ${sync}/VFence.h
    ${sync}/VSemaphore.h

    ${hesabu}/Window/HBaseWindow.h
    ${hesabu}/Window/HWindow.h
)

# compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCES}
    ${PROJECT_HEADERS}
)


set(ENV{VK_LAYER_PATH} "D:/global/VulkanSDK/1.3.296.0/Bin")

# Link dependencies.
set(ENV{VULKAN_SDK} "D:/global/VulkanSDK/1.3.296.0")
find_package(Vulkan REQUIRED)
target_link_libraries(${PROJECT_NAME} Vulkan::Vulkan)
target_include_directories(${PROJECT_NAME} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/${_src})


set(ENV{Eigen3_DIR} "D:/global/Eigen/3.4.0")
find_package(Eigen3 3.3 REQUIRED NO_MODULE)
target_link_libraries(${PROJECT_NAME}  Eigen3::Eigen)

set(ENV{glm_DIR} "D:/global/GLM/1.0.2")
find_package(glm CONFIG REQUIRED)
target_link_libraries(${PROJECT_NAME} glm::glm)

set(STB_PATH "D:/global/STB/1.0.0")
target_include_directories(${PROJECT_NAME} PUBLIC ${STB_PATH})
# target_link_libraries(${PROJECT_NAME} ${STB_PATH})

target_include_directories(${PROJECT_NAME} PUBLIC ${PROJECT_NAME}/Ogun)