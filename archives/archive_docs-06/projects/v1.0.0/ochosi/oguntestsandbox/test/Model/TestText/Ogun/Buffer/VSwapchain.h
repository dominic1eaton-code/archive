/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VSwapchain_h
#define VSwapchain_h

#include "Ogun/Core/VObject.h"
#include <vector>

namespace ogun
{

struct QueueFamilyIndices;

class VSwapchain : public VObject<VSwapchain>
{
public:
    VSwapchain();
    virtual ~VSwapchain(void) = default;
    
    VkSwapchainKHR chain() const { return m_swapchain; }

    VkFormat format() const { return m_surfaceFormat.format; }

    VkExtent2D extent() const { return m_extent; }
                     
    VSwapchain& depth(VkFormat depthFormat);
    
    VSwapchain& memoryProperties(VkPhysicalDeviceMemoryProperties memoryProperties);

    VSwapchain& surface(VkSurfaceKHR surface);

    VSwapchain& extent(VkExtent2D extent);

    VSwapchain& presentModes(const std::vector<VkPresentModeKHR>& presentModes);

    VSwapchain& capabilities(const VkSurfaceCapabilitiesKHR& capabilities);

    VSwapchain& formats(const std::vector<VkSurfaceFormatKHR>& formats);

    VSwapchain& device(VkDevice device);

    VSwapchain& build(VkInstance instance, QueueFamilyIndices indices);

    /* */
    std::vector<VkImage> images() const { return m_images; }

    /* */
    std::vector<VkImageView> imageViews() const { return m_imageViews; }

    void rebuild() 
    {
        // int width = 0, height = 0;
        // glfwGetFramebufferSize(window, &width, &height);
        // while (width == 0 || height == 0) 
        // {
        //     glfwGetFramebufferSize(window, &width, &height);
        //     glfwWaitEvents();
        // }

        // vkDeviceWaitIdle(device);
        // cleanupSwapChain();
        // createSwapChain();
        // createImageViews();
        // createColorResources();
        // createDepthResources();
        // createFramebuffers();
    };

private:
    /* */
    void createImages();

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

    VkSwapchainKHR m_swapchain;

    VkSwapchainCreateInfoKHR m_createInfo;

    VkDevice m_device;

    std::vector<VkSurfaceFormatKHR> m_formats;

    VkSurfaceCapabilitiesKHR m_capabilities;

    std::vector<VkPresentModeKHR> m_presentModes;

    VkExtent2D m_extent;

    VkSurfaceKHR m_surface;

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
    
    VkSurfaceFormatKHR m_surfaceFormat;

    VkPresentModeKHR m_presentMode;

    uint32_t m_imageCount;

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

    /* */
    std::vector<VkImage> m_images;

    /* */
    std::vector<VkImageView> m_imageViews;

    // /* */
    // Image* m_depthImage;
    
    // /* */
    // ImageView* m_depthImageView;

    /* */
    std::vector<VkFramebuffer> m_swapchainFramebuffers;

    /* */
    VkFormat m_depthFormat;

    /* */
    VkPhysicalDeviceMemoryProperties m_memoryProperties;

    /*  mipLevels must be greater than 0 (https://vulkan.lunarg.com/doc/view/1.3.204.0/windows/1.3-extensions/vkspec.html#VUID-VkImageCreateInfo-mipLevels-00947) */
    uint32_t m_mipLevels;
    
    /* */
    VkImageTiling m_tiling;
};

} // namespace ogun

#endif // VSwapchain_h