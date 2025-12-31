# HEADER_PLACEHOLDER
cmake_minimum_required(VERSION 3.18)
#-----------------------------------------------------------
# @brief: Project library file
# @note : N/A
#-----------------------------------------------------------
project(Graphics)

# components
set(_buffer Buffer)
set(_pipeline Pipeline)
set(_math Math)
set(_scene Scene)

# list source files
list(
    APPEND PROJECT_SOURCE
    Renderer.cpp
    ${_buffer}/SwapChain.cpp
    ${_buffer}/Buffer.cpp
    ${_buffer}/VertexBuffer.cpp
    ${_buffer}/StageBuffer.cpp
    ${_buffer}/IndexBuffer.cpp
    ${_buffer}/UniformBuffer.cpp
    ${_buffer}/Descriptor.cpp
    ${_pipeline}/GraphicsPipeline.cpp
    ${_pipeline}/Shader.cpp
    ${_pipeline}/Command.cpp
    ${_pipeline}/ColorPass.cpp
    ${_pipeline}/ImageView.cpp
    ${_pipeline}/Image.cpp
    ${_math}/Primitive.cpp
    ${_math}/Triangle.cpp
    ${_math}/Cube.cpp
    ${_math}/Square.cpp
    ${_scene}/SceneObject.cpp
    ${_scene}/Mesh.cpp
    ${_scene}/Camera.cpp
    ${_scene}/Light.cpp
)

# list headers
list(
    APPEND PROJECT_HEADERS
    Renderer.h
    VulkanDefines.h
    ${_buffer}/SwapChain.h
    ${_buffer}/Buffer.h
    ${_buffer}/VertexBuffer.h
    ${_buffer}/StageBuffer.h
    ${_buffer}/IndexBuffer.h
    ${_buffer}/UniformBuffer.h
    ${_buffer}/Descriptor.h
    ${_buffer}/UniformBufferObject.h
    ${_pipeline}/GraphicsPipeline.h
    ${_pipeline}/Shader.h
    ${_pipeline}/Command.h
    ${_pipeline}/ColorPass.h
    ${_pipeline}/ImageView.h
    ${_pipeline}/Image.h
    ${_math}/Vertex.h
    ${_math}/Primitive.h
    ${_math}/Triangle.h
    ${_math}/Cube.h
    ${_math}/Square.h
    ${_scene}/SceneObject.h
    ${_scene}/Mesh.h
    ${_scene}/Camera.h
    ${_scene}/Light.h
)

# Set compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O2
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O2")
endif()

# Create the library
add_library(
    ${PROJECT_NAME} SHARED
    ${PROJECT_SOURCE}
    ${PROJECT_HEADERS}
)

# link dependencies
global_find_package(Vulkan)
global_find_package(LoggerCPP)
global_find_package(SDL2)
global_find_package(GLM)
global_target_link_libraries(
    Devices
)

# target features
target_compile_features(${PROJECT_NAME} PUBLIC cxx_std_17)
target_include_directories(
    ${PROJECT_NAME} PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}"
)

# setup install targets
global_install(${PROJECT_NAME})

# # check unit tests
# global_check_unit_tests()
