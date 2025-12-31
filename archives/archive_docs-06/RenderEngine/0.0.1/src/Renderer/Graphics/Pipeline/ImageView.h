/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright ; 2023
 */
#pragma once

#ifndef IMAGEVIEW_H
#define IMAGEVIEW_H

#include <string>
#include <vector>
#include <vulkan/vulkan.h>
#include "VulkanDefines.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API ImageView
    {
    public:
        ImageView();
        ImageView(VkDevice device, VkImage image, VkFormat format, VkImageAspectFlags aspectFlags, uint32_t mipLevels);
        virtual ~ImageView();

        /* */
        VkImageView view();
        
        /* */
        void create();

    private:
        /* */
        VkDevice m_device;

        /* */
        VkImageViewCreateInfo m_createInfo;
        
        /* */
        VkImageView m_view;

        /* */
        VkImage m_image;

        /* creation type */
        VkStructureType m_sType;

        /* Pointer to extension structure */
        const void* m_pNext;

        /* instance creation flags */
        VkInstanceCreateFlags m_flags;
        
        /* */
        VkImageViewType m_viewType;
        
        /* */
        VkFormat m_format;
        
        /* */
        VkImageAspectFlags m_aspectFlags;
        
        /* */
        VkComponentMapping m_components;
        
        /* */
       uint32_t m_mipLevels;
    };
}

#endif // IMAGEVIEW_H