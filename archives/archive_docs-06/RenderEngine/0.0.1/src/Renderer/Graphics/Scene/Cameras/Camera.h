/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef CAMERA_H
#define CAMERA_H

#include <glm/glm.hpp>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Buffer/UniformBufferObject.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class Mesh;

    struct GPUCamera : public UniformBufferObject
    {
        alignas(16) glm::mat4 model;
        alignas(16) glm::mat4 view;
        alignas(16) glm::mat4 proj;
        alignas(16) glm::vec3 position;
    };

    class RENGINE_API Camera
    {
    public:
        Camera();
        Camera(GPUCamera data);
        virtual ~Camera(void);

    private:
        GPUCamera* m_data;
    };
}

#endif // CAMERA_H