/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef INDEXBUFFER_H
#define INDEXBUFFER_H

#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Buffer.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API IndexBuffer : public Buffer
    {
    public:
        IndexBuffer();
        IndexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties);
        IndexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size);
        virtual ~IndexBuffer(void);

        /* */
        void map() {};

        /* */
        void map(const std::vector<Vertex> vertices) {};

        /* */
        void map(std::vector<uint16_t> indices) {};
    };
}

#endif // INDEXBUFFER_H
