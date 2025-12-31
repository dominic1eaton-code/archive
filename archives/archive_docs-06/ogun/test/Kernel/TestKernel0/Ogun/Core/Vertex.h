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

namespace ogun
{
    
struct VertexShaderData
{
    glm::vec3 position;
    glm::vec4 color;
    glm::vec2 texture;
    // glm::vec3 normal;

    static std::vector<VkVertexInputBindingDescription> bindingDescription()
    {
        std::vector<VkVertexInputBindingDescription> bindingDescriptions{};
        bindingDescriptions.resize(1);
        bindingDescriptions[0].binding = 0;
        bindingDescriptions[0].stride = sizeof(VertexShaderData);
        bindingDescriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
        return bindingDescriptions;
    }

    static std::array<VkVertexInputAttributeDescription, 3> attributeDescription()
    {
        std::array<VkVertexInputAttributeDescription, 3> attributeDescriptions{};
        attributeDescriptions[0].binding = 0;
        attributeDescriptions[0].location = 0;
        attributeDescriptions[0].format = VK_FORMAT_R32G32B32_SFLOAT;
        attributeDescriptions[0].offset = offsetof(VertexShaderData, position);

        attributeDescriptions[1].binding = 0;
        attributeDescriptions[1].location = 1;
        attributeDescriptions[1].format = VK_FORMAT_R32G32B32A32_SFLOAT;
        attributeDescriptions[1].offset = offsetof(VertexShaderData, color);

        // std::array<VkVertexInputAttributeDescription, 4> attributeDescriptions{};
        attributeDescriptions[2].binding = 0;
        attributeDescriptions[2].location = 2;
        attributeDescriptions[2].format = VK_FORMAT_R32G32_SFLOAT;
        attributeDescriptions[2].offset = offsetof(VertexShaderData, texture);

        // attributeDescriptions[1].binding = 0;
        // attributeDescriptions[1].location = 1;
        // attributeDescriptions[1].format = VK_FORMAT_R32G32B32A32_SFLOAT;
        // attributeDescriptions[1].offset = offsetof(VertexShaderData, color);

        // attributeDescriptions[2].binding = 0;
        // attributeDescriptions[2].location = 2;
        // attributeDescriptions[2].format = VK_FORMAT_R32G32B32_SFLOAT;
        // attributeDescriptions[2].offset = offsetof(VertexShaderData, normal);
    
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

//     // tell Vulkan how to pass this data format to the vertex shader once it's been uploaded into GPU memory
//     struct Vertex
//     {
//         Eigen::Vector3d position;
//         Eigen::Vector3d color;
//         Eigen::Vector3d normal;

//         // vertex binding describes at which rate to load data from memory throughout the vertices. It specifies
//         // the number of bytes between data entries and whether to move to the next data entry after each vertex or
//         // after each instance.
//         static std::vector<VkVertexInputBindingDescription> bindingDescriptions()
//         {
//             std::vector<VkVertexInputBindingDescription> bindingDescriptions{};
//             bindingDescriptions.resize(1);

//             // per-vertex data is packed together in one array, so we're only going to have one binding. The binding
//             // parameter specifies the index of the binding in the array of bindings. The stride parameter specifies
//             // the number of bytes from one entry to the next, and the inputRate parameter can have one of the
//             // following values:
//             //     VK_VERTEX_INPUT_RATE_VERTEX  : Move to the next data entry after each vertex
//             //     VK_VERTEX_INPUT_RATE_INSTANCE: Move to the next data entry after each instance
//             // We're not going to use instanced rendering, so we'll stick to per-vertex data
//             bindingDescriptions[0].binding = 0;
//             bindingDescriptions[0].stride = sizeof(Vertex);
//             bindingDescriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
//             return bindingDescriptions;
//         }

//         // describes how to handle vertex input is VkVertexInputAttributeDescription
//         static std::array<VkVertexInputAttributeDescription, 3> attributeDescriptions()
//         {
//             std::array<VkVertexInputAttributeDescription, 3> attributeDescriptions{};

//             // As the function prototype indicates, there are going to be two of these structures. An attribute description
//             //      struct describes how to extract a vertex attribute from a chunk of vertex data originating from a binding
//             //      description. We have two attributes, position and color, so we need two attribute description structs.
//             //      The binding parameter tells Vulkan from which binding the per-vertex data comes. The location parameter references
//             //      the location directive of the input in the vertex shader. The input in the vertex shader with location 0 is the position
//             //      which has two 32-bit float components.
//             // The format parameter describes the type of data for the attribute. A bit confusingly, the formats are specified
//             //      using the same enumeration as color formats. The following shader types and formats are commonly used together:
//             //     float: VK_FORMAT_R32_SFLOAT
//             //     vec2 : VK_FORMAT_R32G32_SFLOAT
//             //     vec3 : VK_FORMAT_R32G32B32_SFLOAT
//             //     vec4 : VK_FORMAT_R32G32B32A32_SFLOAT
//             attributeDescriptions[0].binding = 0;
//             attributeDescriptions[0].location = 0;
//             attributeDescriptions[0].format = VK_FORMAT_R32G32B32_SFLOAT;
//             attributeDescriptions[0].offset = offsetof(Vertex, position);

//             // As you can see, you should use the format where the amount of color channels matches the number of components in the shader data type.
//             // It is allowed to use more channels than the number of components in the shader, but they will be silently discarded. If the number of
//             // channels is lower than the number of components, then the BGA components will use default values of (0, 0, 1). The color type (SFLOAT, UINT, SINT)
//             // and bit width should also match the type of the shader input. See the following examples:
//             //         ivec2 : VK_FORMAT_R32G32_SINT, a 2-component vector of 32-bit signed integers
//             //         uvec4 : VK_FORMAT_R32G32B32A32_UINT, a 4-component vector of 32-bit unsigned integers
//             //         double: VK_FORMAT_R64_SFLOAT, a double-precision (64-bit) float
//             // The format parameter implicitly defines the byte size of attribute data and the offset parameter specifies the number of bytes since
//             // the start of the per-vertex data to read from. The binding is loading one Vertex at a time and the position attribute (pos) is at an
//             // offset of 0 bytes from the beginning of this struct. This is automatically calculated using the offsetof macro.
//             attributeDescriptions[1].binding = 0;
//             attributeDescriptions[1].location = 1;
//             attributeDescriptions[1].format = VK_FORMAT_R32G32B32_SFLOAT;
//             attributeDescriptions[1].offset = offsetof(Vertex, color);

//             // normal
//             attributeDescriptions[2].binding = 0;
//             attributeDescriptions[2].location = 2;
//             attributeDescriptions[2].format = VK_FORMAT_R32G32B32_SFLOAT;
//             attributeDescriptions[2].offset = offsetof(Vertex, normal);
//             return attributeDescriptions;
//         }
//     };

//     struct RenderObjectIndices
//     {
//         alignas(4)  int light;
//     };
} // namespace ogun

#endif // Vertex_h
