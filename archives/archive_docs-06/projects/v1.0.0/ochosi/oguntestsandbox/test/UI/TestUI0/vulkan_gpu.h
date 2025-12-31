/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#pragma once

#ifndef vulkan_gpu_h
#define vulkan_gpu_h

#include <vector>
#define GLM_FORCE_RADIANS
#define GLM_FORCE_DEPTH_ZERO_TO_ONE
#define GLM_ENABLE_EXPERIMENTAL
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtx/hash.hpp>


namespace ogun
{

#define DIRECTIONAL_LIGHTS_COUNT 1

struct GPUDirLight
{
    alignas(16) glm::vec4 direction;
    alignas(16) glm::vec4 ambient;
    alignas(16) glm::vec4 diffuse;
    alignas(16) glm::vec4 specular;
};

struct GPUCursor
{
    alignas(8) glm::vec2 position;
};

struct GPUView
{
    alignas(16) glm::vec4 position;
};

struct GPUMaterial
{
    alignas(4) float texshininess;
};

struct GPUCamera
{
    /**
     * @brief camera model
     */
    alignas(16) glm::mat4 model;
    
    /**
     * @brief camera view
     */
    alignas(16) glm::mat4 view;
    
    /**
     * @brief camera projection
     */
    alignas(16) glm::mat4 proj;
};

struct GPUMeshData
{
    alignas(16)  glm::mat4 model;
};

struct GPULight
{
    glm::vec4 ambient;
    glm::vec4 diffuse;
    glm::vec4 specular;
};

struct GPULightData
{
    GPULight light;
};

};

#endif // vulkan_gpu_h