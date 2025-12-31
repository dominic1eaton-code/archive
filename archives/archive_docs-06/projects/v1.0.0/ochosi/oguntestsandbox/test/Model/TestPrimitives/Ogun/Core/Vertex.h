/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef Vertex_h
#define Vertex_h

#include <cstddef>
#include <array>
#include <vector>
#include <Eigen/Dense>
#include <vulkan/vulkan.h>

namespace ogun
{
    
struct VertexShaderData
{
    glm::vec3 position;
    glm::vec4 color;
    glm::vec2 texture;
    glm::vec3 normal;

    static std::vector<VkVertexInputBindingDescription> bindingDescription()
    {
        std::vector<VkVertexInputBindingDescription> bindingDescriptions{};
        bindingDescriptions.resize(1);
        bindingDescriptions[0].binding = 0;
        bindingDescriptions[0].stride = sizeof(VertexShaderData);
        bindingDescriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
        return bindingDescriptions;
    }

    static std::array<VkVertexInputAttributeDescription, 4> attributeDescription()
    {
        std::array<VkVertexInputAttributeDescription, 4> attributeDescriptions{};
        attributeDescriptions[0].binding = 0;
        attributeDescriptions[0].location = 0;
        attributeDescriptions[0].format = VK_FORMAT_R32G32B32_SFLOAT;
        attributeDescriptions[0].offset = offsetof(VertexShaderData, position);

        attributeDescriptions[1].binding = 0;
        attributeDescriptions[1].location = 1;
        attributeDescriptions[1].format = VK_FORMAT_R32G32B32A32_SFLOAT;
        attributeDescriptions[1].offset = offsetof(VertexShaderData, color);

        attributeDescriptions[2].binding = 0;
        attributeDescriptions[2].location = 2;
        attributeDescriptions[2].format = VK_FORMAT_R32G32_SFLOAT;
        attributeDescriptions[2].offset = offsetof(VertexShaderData, texture);

        attributeDescriptions[3].binding = 0;
        attributeDescriptions[3].location = 3;
        attributeDescriptions[3].format = VK_FORMAT_R32G32B32_SFLOAT;
        attributeDescriptions[3].offset = offsetof(VertexShaderData, normal);

        // std::array<VkVertexInputAttributeDescription, 4> attributeDescriptions{};
        // attributeDescriptions[1].binding = 0;
        // attributeDescriptions[1].location = 1;
        // attributeDescriptions[1].format = VK_FORMAT_R32G32B32A32_SFLOAT;
        // attributeDescriptions[1].offset = offsetof(VertexShaderData, color);
    
        // attributeDescriptions[3].binding = 0;
        // attributeDescriptions[3].location = 3;
        // attributeDescriptions[3].format = VK_FORMAT_R32G32_SFLOAT;
        // attributeDescriptions[3].offset = offsetof(VertexShaderData, texture);

        return attributeDescriptions;
    }

    bool operator==(const VertexShaderData& other) const 
    {
        return position == other.position && color == other.color; // && normal == other.normal && texture == other.texture;
    }
};

} // namespace ogun

#endif // Vertex_h
