/**
 * @copyright
 * @brief
 * @note
 */

#pragma once
#ifndef vulkan_terrain_h
#define vulkan_terrain_h

#include <cstdint>
#include <vector>
#include <string>
#include <array>
#include <vulkan/vulkan.h>

#define GLM_FORCE_RADIANS
#define GLM_FORCE_DEPTH_ZERO_TO_ONE
#define GLM_ENABLE_EXPERIMENTAL
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtx/hash.hpp>

// #define STB_IMAGE_IMPLEMENTATION
// #include "stb_image.h"
// #include <vulkan/vulkan.h>

namespace ogun
{

struct TVertex
{
    glm::vec3 position;
    glm::vec4 color;
    glm::vec2 texture;

    static std::vector<VkVertexInputBindingDescription> bindingDescription()
    {
        std::vector<VkVertexInputBindingDescription> bindingDescriptions{};
        bindingDescriptions.resize(1);
        bindingDescriptions[0].binding = 0;
        bindingDescriptions[0].stride = sizeof(TVertex);
        bindingDescriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
        return bindingDescriptions;
    }

    static std::array<VkVertexInputAttributeDescription, 3> attributeDescription()
    {
        std::array<VkVertexInputAttributeDescription, 3> attributeDescriptions{};
        attributeDescriptions[0].binding = 0;
        attributeDescriptions[0].location = 0;
        attributeDescriptions[0].format = VK_FORMAT_R32G32B32_SFLOAT;
        attributeDescriptions[0].offset = offsetof(TVertex, position);

        attributeDescriptions[1].binding = 0;
        attributeDescriptions[1].location = 1;
        attributeDescriptions[1].format = VK_FORMAT_R32G32B32A32_SFLOAT;
        attributeDescriptions[1].offset = offsetof(TVertex, color);

        attributeDescriptions[2].binding = 0;
        attributeDescriptions[2].location = 2;
        attributeDescriptions[2].format = VK_FORMAT_R32G32_SFLOAT;
        attributeDescriptions[2].offset = offsetof(TVertex, texture);

        return attributeDescriptions;
    }

    // bool operator==(const TVertex& other) const 
    // {
    //     return position == other.position && color == other.color; // && normal == other.normal && texture == other.texture;
    // }
};


struct GPUTerrain
{

};

class VTerrain
{
public:
    VTerrain() = default;
    virtual ~VTerrain(void) = default;

    std::vector<TVertex> vertices() const { return m_vertices; }

    // void generateVertices();

    // std::vector<glm::vec3> loadHeightMap(std::string heightmap_file);
    void loadHeightMap(uint32_t width, uint32_t height);

private:

    uint8_t resolution = 20u;

    std::vector<TVertex> m_vertices;

    // number of vertices per patch
    const uint8_t TERRAIN_PATCH_VERTICES = 4u;

    uint32_t width;

    uint32_t height;
};


}; // namespace ogun

#endif // vulkan_terrain_h