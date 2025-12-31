/**
 * @copyright DEFAULT
 * @brief: Swapchain wrapper class
 * @note : N/A
 */
#pragma once

#include <vulkan/vulkan.h>
#include <string>

#ifndef Swapchain_H
#define Swapchain_H

namespace LoggingTool
{
    class Logger;
}

namespace RenderEngine
{
    /*
     * Swapchain wrapper class
     */
    // class VKENGINE_API Swapchain
    class Swapchain
    {
    public:
        Swapchain(VInstance* instance);
        virtual ~Swapchain(void);

        /* create swapchain*/
        bool create();

    private:
        /* vulkan object */
        VkSwapchainKHR m_swapChain;

        /* create info */
        VkSwapchainCreateInfoKHR m_createInfo;

        /* specifies the amount of layers each image consists of. This is 
           always 1 unless you are developing a stereoscopic 3D application */
        uint32_t m_imageArrayLayers;

        /* bit field specifies what kind of operations we'll use the 
          images in the swap chain for */
        VkImageUsageFlags m_imageUsage;

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
        
        /* creation type */
        VkStructureType m_sType;

        /* Pointer to extension structure */
        const void* m_pNext;

        /* instance creation flags */
        VkInstanceCreateFlags m_flags;

        /* Logical device reference for creation and destruction of vulkan object */
        VKDevice m_device;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // Swapchain_H