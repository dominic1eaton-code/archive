/**
 * @copyright
 * @brief
 * @note
 */
#pragma once
#ifndef vulkan_shader_h
#define vulkan_shader_h

#include <filesystem>
#include <vulkan/vulkan.h>
#include <glm/glm.hpp>
#include "sema_primitives.h"

namespace vulkan
{


static std::vector<VkVertexInputBindingDescription> particle_vertex_binding()
{
    std::vector<VkVertexInputBindingDescription> binding_descriptions{};
    binding_descriptions.resize(1);
    binding_descriptions[0].binding = 0;
    binding_descriptions[0].stride = sizeof(sema::ParticleVertex);
    binding_descriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
    return binding_descriptions;
};

static std::vector<VkVertexInputAttributeDescription> particle_vertex_attribute()
{
    std::vector<VkVertexInputAttributeDescription> attribute_descriptions{};
    VkVertexInputAttributeDescription attribute{};
    attribute.binding = 0;
    attribute.location = 0;
    attribute.format = VK_FORMAT_R32G32_SFLOAT;
    attribute.offset = offsetof(sema::ParticleVertex, position);
    attribute_descriptions.push_back(attribute);
    
    attribute = {};
    attribute.binding = 0;
    attribute.location = 1;
    attribute.format = VK_FORMAT_R32G32B32A32_SFLOAT;
    attribute.offset = offsetof(sema::ParticleVertex, color);
    attribute_descriptions.push_back(attribute);
    return attribute_descriptions;
}

static std::vector<VkVertexInputBindingDescription> vertex_binding()
{
    std::vector<VkVertexInputBindingDescription> binding_descriptions{};
    binding_descriptions.resize(1);
    binding_descriptions[0].binding = 0;
    binding_descriptions[0].stride = sizeof(sema::Vertex);
    binding_descriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
    return binding_descriptions;
};

static std::vector<VkVertexInputAttributeDescription> vertex_attribute()
{
    std::vector<VkVertexInputAttributeDescription> attribute_descriptions{};
    VkVertexInputAttributeDescription attribute{};
    attribute.binding = 0;
    attribute.location = 0;
    attribute.format = VK_FORMAT_R32G32B32A32_SFLOAT;
    attribute.offset = offsetof(sema::Vertex, color);
    attribute_descriptions.push_back(attribute);
    
    attribute = {};
    attribute.binding = 0;
    attribute.location = 1;
    attribute.format = VK_FORMAT_R32G32B32_SFLOAT;
    attribute.offset = offsetof(sema::Vertex, position);
    attribute_descriptions.push_back(attribute);
    
    attribute = {};
    attribute.binding = 0;
    attribute.location = 2;
    attribute.format = VK_FORMAT_R32G32B32_SFLOAT;
    attribute.offset = offsetof(sema::Vertex, normal);
    attribute_descriptions.push_back(attribute);
    
    attribute = {};
    attribute.binding = 0;
    attribute.location = 3;
    attribute.format = VK_FORMAT_R32G32B32_SFLOAT;
    attribute.offset = offsetof(sema::Vertex, tangent);
    attribute_descriptions.push_back(attribute);
    
    attribute = {};
    attribute.binding = 0;
    attribute.location = 4;
    attribute.format = VK_FORMAT_R32G32B32_SFLOAT;
    attribute.offset = offsetof(sema::Vertex, bitangent);
    attribute_descriptions.push_back(attribute);
    
    attribute = {};
    attribute.binding = 0;
    attribute.location = 5;
    attribute.format = VK_FORMAT_R32G32B32_SFLOAT;
    attribute.offset = offsetof(sema::Vertex, texture);
    attribute_descriptions.push_back(attribute);
    return attribute_descriptions;
}



void init_shaders(std::filesystem::path asset_library_path);

}; // namespace vulkan

#endif // vulkan_shader_h