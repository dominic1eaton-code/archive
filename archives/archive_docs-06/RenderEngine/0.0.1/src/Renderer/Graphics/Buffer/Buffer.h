/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef BUFFER_H
#define BUFFER_H

#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Math/Vertex.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API Buffer
    {
    public:
        Buffer();
        Buffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties);
        Buffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties);
        virtual ~Buffer(void);

        /* */
        void allocate(VkDeviceSize size);

        /* */
        VkBuffer buffer();

        /* */
        VkDeviceSize size();

        /* */
        void deallocate();

        /* */
        void unmap();

    protected:
        /* */
        void create();

        /* */
        uint32_t findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties);

        /* */
        virtual void map() = 0;

        /* */
        virtual void map(const std::vector<Vertex> vertices) = 0;

        /* */
        virtual void map(std::vector<uint16_t> indices) = 0;


        /* */
        VkDeviceSize m_size;

        /* */
        VkBufferUsageFlags m_usage;

        /* */
        VkMemoryPropertyFlags m_properties;

        /* creation type */
        VkStructureType m_sType;

        /* Pointer to extension structure */
        const void* m_pNext;

        /* instance creation flags */
        VkInstanceCreateFlags m_flags;

        /* */
        VkSharingMode m_sharingMode;

        /* */
        VkDevice m_device;

        /* */
        VkBuffer m_buffer;

        /* */
        VkBufferCreateInfo m_bufferInfo;

        /* */
        VkDeviceMemory m_bufferMemory;

        /* */
        VkMemoryAllocateInfo m_allocInfo;

        /* */
        VkMemoryRequirements m_memoryRequirements;

        /* */
        VkPhysicalDeviceMemoryProperties m_memoryProperties;

    };
}

#endif // BUFFER_H
