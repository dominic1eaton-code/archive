# @header 
# @copyright
# @brief
# @note
cmake_minimum_required(VERSION 3.18)
project(TestKernel0)

set(ogun Ogun)
set(core Ogun/Core)
set(buffer Ogun/Buffer)
set(hesabu Hesabu)

# source files
list(
    APPEND PROJECT_SOURCES

    main.cpp

    ${core}/VInstance.cpp
    ${core}/VDevice.cpp
    ${core}/VSurface.cpp
    ${core}/VShader.cpp
    ${core}/VPipeline.cpp
    ${core}/VDescriptor.cpp
    # ${core}/VImage.cpp
    # ${core}/VCommand.cpp
    ${core}/VShaderManager.cpp
    ${core}/VSyncManager.cpp

    ${buffer}/VFrameBuffer.cpp
    ${buffer}/VSwapchain.cpp
    
    ${hesabu}/Window/HWindow.cpp

)

# headers files
list(
    APPEND PROJECT_HEADERS
    
    ${core}/VObject.h
    ${core}/VDevice.h
    ${core}/VSurface.h
    ${core}/VShader.h
    ${core}/VFile.h
    ${core}/VPipeline.h
    ${core}/Vertex.h
    ${core}/VDescriptor.h
    ${core}/VConstants.h
    # ${core}/VImage.h
    # ${core}/VCommand.h
    ${core}/VShaderManager.h
    ${core}/VSyncManager.h

    ${buffer}/VFrameBuffer.h
    ${buffer}/VSwapchain.h
    
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


set(ENV{VK_LAYER_PATH} "C:/global/VulkanSDK/1.3.296.0/Bin")

# Link dependencies.
set(ENV{VULKAN_SDK} "C:/global/VulkanSDK/1.3.296.0")
find_package(Vulkan REQUIRED)
target_link_libraries(${PROJECT_NAME} Vulkan::Vulkan)
target_include_directories(${PROJECT_NAME} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/${_src})


set(ENV{Eigen3_DIR} "C:/global/Eigen/3.4.0")
find_package(Eigen3 3.3 REQUIRED NO_MODULE)
target_link_libraries(${PROJECT_NAME}  Eigen3::Eigen)

target_include_directories(${PROJECT_NAME} PUBLIC ${PROJECT_NAME}/Ogun)