/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VSwapchain.h"
#include "Ogun/Core/VDevice.h"
#include <cstdint>   // Necessary for uint32_t
#include <limits>    // Necessary for std::numeric_limits
#include <algorithm> // Necessary for std::clamp
#include "Ogun/Core/VConstants.h"

// #define NOMINMAX
// #undef max

using namespace ogun;


VSwapchain::VSwapchain()
    : m_swapchain(VK_NULL_HANDLE)
    , m_createInfo({})
    , m_imageArrayLayers(1u)
    , m_imageUsage(VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT)
    , m_imageSharingMode(VK_SHARING_MODE_EXCLUSIVE)
    , m_queueFamilyIndexCount(0u)
    , m_pQueueFamilyIndices(nullptr)
    , m_compositeAlpha(VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR)
    , m_clipped(VK_TRUE)
    , m_oldSwapchain(VK_NULL_HANDLE)
    , m_imageCount(0u)
    , m_mipLevels(1u)
    , m_tiling(VK_IMAGE_TILING_OPTIMAL)
    , m_images({})
{}

VSwapchain& VSwapchain::depth(VkFormat depthFormat)
{
    m_depthFormat = depthFormat;
    return *this;
}

VSwapchain& VSwapchain::memoryProperties(VkPhysicalDeviceMemoryProperties memoryProperties)
{
    m_memoryProperties = memoryProperties;
    return *this;
}

VSwapchain& VSwapchain::surface(VkSurfaceKHR surface)
{
    m_surface = surface;
    return *this;
}

VSwapchain& VSwapchain::extent(VkExtent2D extent)
{
    m_extent = extent;
    return *this;
}

VSwapchain& VSwapchain::presentModes(const std::vector<VkPresentModeKHR>& presentModes)
{
    m_presentModes = presentModes;
    return *this;
}

VSwapchain& VSwapchain::capabilities(const VkSurfaceCapabilitiesKHR& capabilities)
{
    m_capabilities = capabilities;
    return *this;
}

VSwapchain& VSwapchain::formats(const std::vector<VkSurfaceFormatKHR>& formats)
{
    m_formats = formats;
    return *this;
}

VSwapchain& VSwapchain::device(VkDevice device)
{
    m_device = device;
    return *this;
}

VSwapchain& VSwapchain::build(VkInstance instance, QueueFamilyIndices indices)
{
    m_surfaceFormat = selectSwapSurfaceFormat(m_formats);
    m_presentMode = selectSwapPresentMode(m_presentModes);
    m_extent = selectSwapExtent(m_capabilities, m_extent);
    if (m_capabilities.minImageCount + 1 == constants::MAX_FRAMES_IN_FLIGHT)
    {
         m_imageCount = m_capabilities.minImageCount + 1;
    }
    else
    {
        m_imageCount = constants::MAX_FRAMES_IN_FLIGHT;
    }
   
    if (m_capabilities.maxImageCount > 0 && m_imageCount > m_capabilities.maxImageCount)
    {
        m_imageCount = m_capabilities.maxImageCount;
    }
    // if (indices.graphicsAndComputeFamily != indices.presentFamily)
    // {
    //     m_imageSharingMode = VK_SHARING_MODE_CONCURRENT;
    //     m_queueFamilyIndexCount = 2;
    //     m_pQueueFamilyIndices = queueFamilyIndices;
    // } 
    // else 
    // {
    //     m_imageSharingMode = VK_SHARING_MODE_EXCLUSIVE;
    // }
    // specify the current transformation to indicate no pre transformation is desired
    m_preTransform = m_capabilities.currentTransform;

    m_createInfo.sType = VK_STRUCTURE_TYPE_SWAPCHAIN_CREATE_INFO_KHR;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0;
    m_createInfo.surface = m_surface;
    m_createInfo.minImageCount = m_imageCount;
    m_createInfo.imageFormat = m_surfaceFormat.format;
    m_createInfo.imageColorSpace = m_surfaceFormat.colorSpace;
    m_createInfo.imageExtent = m_extent;
    m_createInfo.imageArrayLayers = m_imageArrayLayers;
    m_createInfo.imageUsage = m_imageUsage;
    m_createInfo.imageSharingMode = m_imageSharingMode;
    m_createInfo.queueFamilyIndexCount = m_queueFamilyIndexCount;
    m_createInfo.pQueueFamilyIndices = m_pQueueFamilyIndices;
    m_createInfo.preTransform = m_capabilities.currentTransform;;
    m_createInfo.compositeAlpha = m_compositeAlpha;
    m_createInfo.presentMode = m_presentMode;
    m_createInfo.clipped = m_clipped;
    m_createInfo.oldSwapchain = m_oldSwapchain;
    
    createvk(vkCreateSwapchainKHR(m_device,
                                 &m_createInfo,
                                 nullptr,
                                 &m_swapchain));
    createImages();
    return *this;
}

void VSwapchain::createImages()
{
    vkGetSwapchainImagesKHR(m_device, m_swapchain, &m_imageCount, nullptr);
    m_images.resize(m_imageCount);
    vkGetSwapchainImagesKHR(m_device, m_swapchain, &m_imageCount, m_images.data());
    
    m_imageViews.resize(m_images.size());
    for (size_t i = 0; i < m_images.size(); i++) {
        VkImageViewCreateInfo createInfo{};
        createInfo.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
        createInfo.image = m_images[i];
        createInfo.viewType = VK_IMAGE_VIEW_TYPE_2D;
        createInfo.format = m_surfaceFormat.format;
        createInfo.components.r = VK_COMPONENT_SWIZZLE_IDENTITY;
        createInfo.components.g = VK_COMPONENT_SWIZZLE_IDENTITY;
        createInfo.components.b = VK_COMPONENT_SWIZZLE_IDENTITY;
        createInfo.components.a = VK_COMPONENT_SWIZZLE_IDENTITY;
        createInfo.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        createInfo.subresourceRange.baseMipLevel = 0;
        createInfo.subresourceRange.levelCount = 1;
        createInfo.subresourceRange.baseArrayLayer = 0;
        createInfo.subresourceRange.layerCount = 1;
        
        createvk(vkCreateImageView(m_device,
                                        &createInfo,
                                        nullptr,
                                        &m_imageViews[i]));
    }
}

VkSurfaceFormatKHR VSwapchain::selectSwapSurfaceFormat(const std::vector<VkSurfaceFormatKHR>& availableFormats) 
{
    // Each VkSurfaceFormatKHR entry contains a format and a colorSpace member. The format member 
    // specifies the color channels and types. For example, VK_FORMAT_B8G8R8A8_SRGB means that we 
    // store the B, G, R and alpha channels in that order with an 8 bit unsigned integer for a total 
    // of 32 bits per pixel. The colorSpace member indicates if the SRGB color space is supported or 
    // not using the VK_COLOR_SPACE_SRGB_NONLINEAR_KHR flag. For the color space we'll use SRGB if
    // it is available
    // @reference:
    //      https://stackoverflow.com/questions/12524623/what-are-the-practical-differences-when-working-with-colors-in-a-linear-vs-a-no
    for (const auto& availableFormat : availableFormats)
    {
        if (availableFormat.format == VK_FORMAT_B8G8R8A8_SRGB && availableFormat.colorSpace == VK_COLOR_SPACE_SRGB_NONLINEAR_KHR) 
        {
            return availableFormat;
        }
    }
    return availableFormats[0];
}

VkPresentModeKHR VSwapchain::selectSwapPresentMode(const std::vector<VkPresentModeKHR>& availablePresentModes) 
{
    // represents the actual conditions for showing images to the screen. There are four
    // possible modes available in Vulkan:
    // VK_PRESENT_MODE_IMMEDIATE_KHR   : Images submitted by your application are transferred to the
    //                                   screen right away, which may result in tearing.
    // VK_PRESENT_MODE_FIFO_KHR        : The swap chain is a queue where the display takes an image from the front
    //                                   of the queue when the display is refreshed and the program inserts rendered
    //                                   images at the back of the queue. If the queue is full then the program has
    //                                   to wait. This is most similar to vertical sync as found in modern games. The
    //                                   moment that the display is refreshed is known as "vertical blank". On mobile 
    //                                   devices, where energy usage is more important, will probably want to use.
    // VK_PRESENT_MODE_FIFO_RELAXED_KHR: This mode only differs from the previous one if the application is late and
    //                                   the queue was empty at the last vertical blank. Instead of waiting for the next
    //                                   vertical blank, the image is transferred right away when it finally arrives.
    //                                   This may result in visible tearing. It allows us to avoid tearing while still 
    //                                   maintaining a fairly low latency by rendering new images that are as up-to-date 
    //                                   as possible right until the vertical blank
    // VK_PRESENT_MODE_MAILBOX_KHR     : This is another variation of the second mode. Instead of blocking the application
    //                                   when the queue is full, the images that are already queued are simply replaced
    //                                   with the newer ones. This mode can be used to render frames as fast as possible
    //                                   while still avoiding tearing, resulting in fewer latency issues than standard vertical
    //                                   sync. This is commonly known as "triple buffering", although the existence of three
    //                                   buffers alone does not necessarily mean that the framerate is unlocked.
    // @note Only the VK_PRESENT_MODE_FIFO_KHR mode is guaranteed to be available
    for (const auto& availablePresentMode : availablePresentModes)
    {
        if (availablePresentMode == VK_PRESENT_MODE_MAILBOX_KHR)
        {
            return availablePresentMode;
        }
    }
    return VK_PRESENT_MODE_FIFO_KHR;
}

VkExtent2D VSwapchain::selectSwapExtent(const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent)
{
    // The swap extent is the resolution of the swap chain images and it's almost
    // always exactly equal to the resolution of the window that we're drawing
    // to in pixels. The range of the possible resolutions is defined in the
    // VkSurfaceCapabilitiesKHR structure. Vulkan tells us to match the resolution 
    // of the window by setting the width and height in the currentExtent member.
    // However, some window managers do allow us to differ here and this is indicated 
    // by setting the width and height in currentExtent to a special value: the maximum 
    // value of uint32_t. In that case we'll pick the resolution that best matches the 
    // window within the minImageExtent and maxImageExtent bounds. But we must specify 
    // the resolution in the correct unit.
    if(capabilities.currentExtent.width != (std::numeric_limits<uint32_t>::max)())
    {
        return capabilities.currentExtent;
    } 
    else
    {
        VkExtent2D actualExtent = {
            static_cast<uint32_t>(extent.width),
            static_cast<uint32_t>(extent.height)
        };

        actualExtent.width = std::clamp(actualExtent.width, capabilities.minImageExtent.width, capabilities.maxImageExtent.width);
        actualExtent.height = std::clamp(actualExtent.height, capabilities.minImageExtent.height, capabilities.maxImageExtent.height);
        return actualExtent;
    }
}