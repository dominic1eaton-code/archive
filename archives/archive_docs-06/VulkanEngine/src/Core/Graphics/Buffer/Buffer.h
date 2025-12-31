/**
 * @file
 * @brief
 * @author
 * @note
 */
#pragma once

#ifndef BUFFER_H
#define BUFFER_H

#include "Utility/VulkanDefines.h"
#include "Utility/VulkanCommonIncludes.h"

namespace VulkanEngine
{
    class VulkanLogger;
    class VKENGINE_API Buffer
    {
        public:
            Buffer();
            virtual ~Buffer(void);
            VkBuffer createBuffer();
            VkDeviceMemory allocate();
            void initialize(VkDevice logicalDevice, VkMemoryRequirements memoryRequirements);

        protected:
            VkBufferCreateInfo m_createInfo;   
            VkStructureType     m_sType;
            const void*         m_pNext;
            VkBufferCreateFlags m_flags;
            VkDeviceSize        m_size;
            VkBufferUsageFlags  m_usage;
            VkSharingMode       m_sharingMode;
            uint32_t            m_queueFamilyIndexCount;
            const uint32_t*     m_pQueueFamilyIndices;
            VkMemoryRequirements m_memoryRequirements;
            VkDevice m_logicalDevice;
            VkBuffer  m_buffer;
            VkDeviceMemory m_memory;   
            VulkanLogger* m_logger;

            /*
             * Graphics cards can offer different types of memory 
             * to allocate from. Each type of memory varies in 
             * terms of allowed operations and performance characteristics.
             * We need to combine the requirements of the buffer and our 
             * own application requirements to find the right type of
             * memory to use
             */
            uint32_t findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties);
            void copy();
    };
}
#endif