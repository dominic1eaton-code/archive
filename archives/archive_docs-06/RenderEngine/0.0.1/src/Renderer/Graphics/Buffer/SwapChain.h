/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef SWAPCHAIN_H
#define SWAPCHAIN_H

#include <string>
#include <vector>
#include <vulkan/vulkan.h>
#include "VulkanDefines.h"
#include "PhysicalDevice.h"

// forward declerations
namespace LoggingTool { class Logger; }
// class VkDevice;

namespace RenderEngine
{
   class ImageView;
   class Image;

    class RENGINE_API SwapChain
    {
    public:
        SwapChain();
        SwapChain(VkDevice device, QueueFamilyIndices indices, VkSurfaceKHR surface,
                     const std::vector<VkSurfaceFormatKHR>& formats, const std::vector<VkPresentModeKHR>& presentModes,
                     const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent, VkFormat depthFormat,
                     VkPhysicalDeviceMemoryProperties memoryProperties);
        virtual ~SwapChain(void);

        /* create swapchain */
        bool create(QueueFamilyIndices indices, VkSurfaceKHR surface,
                    const std::vector<VkSurfaceFormatKHR>& formats, const std::vector<VkPresentModeKHR>& presentModes,
                    const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent);

         /* */
         std::vector<VkImageView> imageViews();

         /* */
         VkExtent2D extent() const;

         /* */
         VkFormat format() const;

         /* */
         VkSwapchainKHR buffer() const;

         /* */
         std::vector<VkFramebuffer> framebuffers() const;

         /* */
         bool createFrameBuffers(VkRenderPass renderPass);

    private:
         /*
         * Each VkSurfaceFormatKHR entry contains a 
         * format and a colorSpace member. The format
         * member specifies the color channels and types
         */
         VkSurfaceFormatKHR selectSwapSurfaceFormat(const std::vector<VkSurfaceFormatKHR>& availableFormats);

         /*
         * represents the actual conditions for
         * showing images to the screen
         */
         VkPresentModeKHR selectSwapPresentMode(const std::vector<VkPresentModeKHR>& availablePresentModes);

         /*
         * The swap extent is the resolution of the
         * swap chain images and it's almost always
         * exactly equal to the resolution of the
         * window that we're drawing to in pixels
         */
         VkExtent2D selectSwapExtent(const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent);

         /* */
         void createImageViews(uint32_t imageCount);

         /* */
         uint32_t m_imageCount;

         /* */
         VkDevice m_device;

         /* vulkan object */
         VkSwapchainKHR m_swapChain;

         /* create info */
         VkSwapchainCreateInfoKHR m_createInfo;

         /* */
         VkSurfaceFormatKHR m_surfaceFormat;

         /* */
         VkPresentModeKHR m_presentMode;

         /* */
         VkExtent2D m_extent;

         /* specifies the amount of layers each image consists of. This is 
            always 1 unless you are developing a stereoscopic 3D application */
         uint32_t m_imageArrayLayers;

         /* bit field specifies what kind of operations we'll use the 
            images in the swap chain for */
         VkImageUsageFlags m_imageUsage;

         /* */
         VkSharingMode m_imageSharingMode;

         /* */
         uint32_t m_queueFamilyIndexCount;

         /* */
         const uint32_t* m_pQueueFamilyIndices;

         /* field specifies if the alpha channel should be used for blending 
            with other windows in the window system. You'll almost always want 
            to simply ignore the alpha channel, hence VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR */
         VkCompositeAlphaFlagBitsKHR m_compositeAlpha;

         /* If set to VK_TRUE then that means that we don't care about the color of 
            pixels that are obscured, for example because another window is in front 
            of them. Unless you really need to be able to read these pixels back and 
            get predictable results, you'll get the best performance by enabling clipping. */
         VkBool32 m_clipped;

         /* With Vulkan it's possible that your swap chain becomes invalid or unoptimized 
            while your application is running, for example because the window was resized.
            In that case the swap chain actually needs to be recreated from scratch and a 
            reference to the old one must be specified in this field */
         VkSwapchainKHR m_oldSwapchain;

         /* We can specify that a certain transform should be applied to images in the swap chain if 
            it is supported (supportedTransforms in capabilities), like a 90 degree clockwise rotation 
            or horizontal flip. To specify that you do not want any transformation, simply specify the 
            current transformation. */
         VkSurfaceTransformFlagBitsKHR m_preTransform;

         /* */
         std::vector<VkImage> m_swapChainImages;

         /* */
         std::vector<ImageView*> m_swapChainImageViews;

         /* */
         Image* m_depthImage;
         
         /* */
         ImageView* m_depthImageView;

         /* */
         std::vector<VkFramebuffer> m_swapChainFramebuffers;

         /* */
         VkFormat m_depthFormat;

         /* */
         VkPhysicalDeviceMemoryProperties m_memoryProperties;

         /*  mipLevels must be greater than 0 (https://vulkan.lunarg.com/doc/view/1.3.204.0/windows/1.3-extensions/vkspec.html#VUID-VkImageCreateInfo-mipLevels-00947) */
         uint32_t m_mipLevels;
         
         /* */
         VkImageTiling m_tiling;

         /* creation type */
         VkStructureType m_sType;

         /* Pointer to extension structure */
         const void* m_pNext;

         /* instance creation flags */
         VkInstanceCreateFlags m_flags;

         /* */
         bool m_created;

         /* Logging unit */
         LoggingTool::Logger* m_logger;

         /* Logging unit */
         std::string m_logunit;
    };
}

#endif // SWAPCHAIN_H