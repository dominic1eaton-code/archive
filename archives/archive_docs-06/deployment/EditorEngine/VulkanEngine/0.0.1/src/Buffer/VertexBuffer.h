/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef VERTEXBUFFER_H
#define VERTEXBUFFER_H

#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Buffer.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API VertexBuffer : public Buffer
    {
    public:
        VertexBuffer();
        VertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties);
        VertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size);
        virtual ~VertexBuffer(void);

        /* */
        void map() {};

        /* */
        void map(const std::vector<Vertex> vertices) {};

        /* */
        void map(std::vector<uint16_t> indices) {};
    };
}

#endif // VERTEXBUFFER_H
