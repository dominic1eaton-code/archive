/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef UNIFORMBUFFER_H
#define UNIFORMBUFFER_H

#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Buffer.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    struct UniformBufferObject;

    class RENGINE_API UniformBuffer : public Buffer
    {
    public:
        UniformBuffer();
        UniformBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDescriptorType type, uint32_t binding);
        UniformBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDescriptorType type, uint32_t binding, VkBufferUsageFlags usage);
        UniformBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size);
        virtual ~UniformBuffer(void);

        /* */
        void map();

        /* */
        void map(const std::vector<Vertex> vertices) {};

        /* */
        void map(std::vector<uint16_t> indices) {};

        /* */
        void copy(UniformBufferObject data);

        /* */
        void* buffersMapped();

        /* */
        VkDescriptorType type();

        /* */
        uint32_t binding();

    protected:
        /* */
        void* m_buffersMapped;

        /* */
        VkDescriptorType m_type;

        /* */
        uint32_t m_binding;
    };
}

#endif // UNIFORMBUFFER_H
