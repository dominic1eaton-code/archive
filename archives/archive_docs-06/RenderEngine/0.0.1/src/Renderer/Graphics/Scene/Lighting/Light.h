/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef LIGHT_H
#define LIGHT_H

#include <glm/glm.hpp>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Buffer/UniformBufferObject.h"
#include "SceneObject.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class Mesh;

    struct GPULight : public UniformBufferObject
    {
        alignas(16) glm::vec3 ambient;
        alignas(16) glm::vec3 diffuse;
        alignas(16) glm::vec3 specular;
        alignas(4)  float     shine;
    };

    class RENGINE_API Light : public SceneObject
    {
    public:
        Light();
        virtual ~Light(void);

    private:
        /* */
        Mesh* m_mesh;

        /* */
        GPULight m_gpu;

        /* */
        glm::vec3 m_ambient;

        /* */
        glm::vec3 m_diffuse;

        /* */
        glm::vec3 m_specular;

        /* */
        float m_shine;
    };
}

#endif // LIGHT_H