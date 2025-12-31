/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef MATERIAL_H
#define MATERIAL_H

#include <vector>
#include <glm/glm.hpp>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Buffer/UniformBufferObject.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class Mesh;
    class Texture;

    struct GPUMaterial : public UniformBufferObject
    {
        alignas(16) glm::vec3 ambient;
        alignas(16) glm::vec3 diffuse;
        alignas(16) glm::vec3 specular;
        alignas(4)  float     shine;
    };

    class RENGINE_API Material
    {
    public:
        Material();
        Material(GPUMaterial data);
        virtual ~Material(void);

    private:
        /* */
        std::vector<Texture*> m_textures;

        GPUMaterial m_data;
    };
}

#endif // MATERIAL_H