/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright ; 2023
 */
#pragma once

#ifndef IMAGE_H
#define IMAGE_H

#include <string>
#include <vector>
#include <vulkan/vulkan.h>
#include "VulkanDefines.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API Image
    {
    public:
        Image();
        Image(VkDevice device, VkFormat format, VkExtent3D extent, uint32_t mipLevels, VkImageTiling tiling, VkImageUsageFlags usage, VkMemoryPropertyFlags memoryProperties, VkPhysicalDeviceMemoryProperties deviceMemoryProperties);
        virtual ~Image();

        /* */
        VkImage image();

        /* */
        void create();

    private:
        /* */
        VkImage m_image;

        /* */
        VkImageCreateInfo m_imageInfo;

        /* */
        VkMemoryAllocateInfo m_allocInfo;

        /* */
        VkDeviceMemory m_imageMemory;

        /* */
        VkDevice m_device;

        /* */
        uint32_t m_memoryTypeIndex;
        
        /* creation type */
        VkStructureType m_sType;

        /* Pointer to extension structure */
        const void* m_pNext;

        /* instance creation flags */
        VkInstanceCreateFlags m_flags;

        /* */
        VkImageType  m_imageType;
        
        /* */
        VkFormat m_format;
        
        /* */
        VkExtent3D m_extent;
        
        /* */
        uint32_t m_mipLevels;
        
        /* */
        uint32_t m_arrayLayers;
        
        /* */
        VkSampleCountFlagBits m_samples;
        
        /* */
        VkImageTiling m_tiling;
        
        /* */
        uint32_t m_queueFamilyIndexCount;
        
        /* */
        VkImageUsageFlags m_usage;
        
        /* */
        VkSharingMode m_sharingMode;
        
        /* */
        const uint32_t* m_pQueueFamilyIndices;
        
        /* */
        VkImageLayout m_initialLayout;
        
        /* */
        VkMemoryPropertyFlags m_memoryProperties;
        
        /* */
        VkPhysicalDeviceMemoryProperties m_deviceMemoryProperties;
    };
}

#endif // IMAGE_H