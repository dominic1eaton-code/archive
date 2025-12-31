# @header 
# @copyright
# @brief
# @note
cmake_minimum_required(VERSION 3.18)
project(OVulkan)

# source files
list(
    APPEND PROJECT_SOURCES
    
    main.cpp
    ogun_app.cpp
    hesabu_window.cpp
    vulkan_engine.cpp
    vulkan_model.cpp
    vulkan_shader.cpp
    ogun_scene.cpp
    sema_primitives.cpp
    sema_math.cpp
    ogun_model.cpp
)

# headers files
list(
    APPEND PROJECT_HEADERS

    ogun_app.h
    hesabu_window.h
    vulkan_engine.h
    vulkan_model.h
    vulkan_shader.h
    ogun_scene.h
    sema_primitives.h
    sema_math.h
    ogun_model.h
)

# compiler flags
if(CMAKE_COMPILER_IS_GNUCXX)
    # Optimization level -O3
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3")
endif()

add_executable(
    ${PROJECT_NAME}
    ${PROJECT_SOURCES}
    ${PROJECT_HEADERS}
)

if (UNIX)
    find_package(X11 REQUIRED)
    target_include_directories(${PROJECT_NAME} PUBLIC ${X11_INCLUDE_DIR})
    target_link_libraries(${PROJECT_NAME} ${X11_LIBRARIES})
endif()

# add dependencies
common_find_package(Vulkan)
common_find_package(STB)
common_find_package(Eigen3)
common_find_package(glm)
# common_find_package(assimp)