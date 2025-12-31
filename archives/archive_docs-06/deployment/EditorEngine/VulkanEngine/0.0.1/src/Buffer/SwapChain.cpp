/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#define NOMINMAX
#include "SwapChain.h"
#include "Logger.h"
#include "VulkanCommon.h"
#include "Pipeline/ImageView.h"
#include "Pipeline/Image.h"
#include <array>
#include <cstdint>   // Necessary for uint32_t
#include <limits>    // Necessary for std::numeric_limits
#include <algorithm> // Necessary for std::clamp


using namespace RenderEngine;

SwapChain::SwapChain()
{}

SwapChain::SwapChain(VkDevice device, QueueFamilyIndices indices, VkSurfaceKHR surface,
                     const std::vector<VkSurfaceFormatKHR>& formats, const std::vector<VkPresentModeKHR>& presentModes,
                     const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent, VkFormat depthFormat,
                     VkPhysicalDeviceMemoryProperties memoryProperties)
    : m_logunit("Swapchain")
    , m_swapChain(VK_NULL_HANDLE)
    , m_createInfo({})
    , m_sType(VK_STRUCTURE_TYPE_SWAPCHAIN_CREATE_INFO_KHR)
    , m_pNext(NULL)
    , m_flags(0)
    , m_imageArrayLayers(1u)
    , m_imageUsage(VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT)
    , m_imageSharingMode(VK_SHARING_MODE_EXCLUSIVE)
    , m_queueFamilyIndexCount(0)
    , m_pQueueFamilyIndices(nullptr)
    , m_compositeAlpha(VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR)
    , m_clipped(VK_TRUE)
    , m_oldSwapchain(VK_NULL_HANDLE)
    , m_device(device)
    , m_imageCount(0)
    , m_depthFormat(depthFormat)
    , m_memoryProperties(memoryProperties)
    , m_mipLevels(1)
    , m_tiling(VK_IMAGE_TILING_OPTIMAL)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    create(indices, surface, formats, presentModes, capabilities, extent);
}

SwapChain::~SwapChain()
{
    vkDestroySwapchainKHR(m_device, m_swapChain, nullptr);
    for (auto imageView : m_swapChainImageViews) { vkDestroyImageView(m_device, imageView->view(), nullptr); }
}

bool SwapChain::create(QueueFamilyIndices indices, VkSurfaceKHR surface,
                     const std::vector<VkSurfaceFormatKHR>& formats, const std::vector<VkPresentModeKHR>& presentModes,
                     const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent)
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Creating swapchain" << LoggingTool::Logger::endl;

    // get swap chain attributes
    m_surfaceFormat = selectSwapSurfaceFormat(formats);
    m_presentMode = selectSwapPresentMode(presentModes);
    m_extent = selectSwapExtent(capabilities, extent);

    // have to decide how many images we would like to have in the swap chain.
    // The implementation specifies the minimum number that it requires to 
    // function. However, simply sticking to this minimum means that we may sometimes
    // have to wait on the driver to complete internal operations before we can acquire 
    // another image to render to. Therefore it is recommended to request at least one
    // more image than the minimum:
    uint32_t imageCount = capabilities.minImageCount + 1;

    // We should also make sure to not exceed the maximum number of images while doing 
    // this, where 0 is a special value that means that there is no maximum:
    if (capabilities.maxImageCount > 0 && imageCount > capabilities.maxImageCount)
    {
        imageCount = capabilities.maxImageCount;
    }
    m_imageCount = imageCount;

    // we need to specify how to handle swap chain images that will be used across multiple queue 
    // families. That will be the case in our application if the graphics queue family is different 
    // from the presentation queue. We'll be drawing on the images in the swap chain from the graphics 
    // queue and then submitting them on the presentation queue. There are two ways to handle images 
    // that are accessed from multiple queues:
    // VK_SHARING_MODE_EXCLUSIVE : An image is owned by one queue family at a time and ownership
    //                             must be explicitly transferred before using it in another queue
    //                             family. This option offers the best performance.
    // VK_SHARING_MODE_CONCURRENT: Images can be used across multiple queue families without explicit
    //                             ownership transfers.
    uint32_t queueFamilyIndices[] = {indices.graphicsFamily.value(), indices.presentFamily.value()};
    if (indices.graphicsFamily != indices.presentFamily) 
    {
        m_imageSharingMode = VK_SHARING_MODE_CONCURRENT;
        m_queueFamilyIndexCount = 2;
        m_pQueueFamilyIndices = queueFamilyIndices;
    }
    else 
    {
        m_imageSharingMode = VK_SHARING_MODE_EXCLUSIVE;
        m_queueFamilyIndexCount = 0;       // Optional
        m_pQueueFamilyIndices = nullptr;   // Optional
    }

    // specify the current transformation to indicate no pre transformation is desired
    m_preTransform = capabilities.currentTransform;

    // populate vulkan object create info
    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.surface = surface;
    m_createInfo.minImageCount = m_imageCount;
    m_createInfo.imageFormat = m_surfaceFormat.format;
    m_createInfo.imageColorSpace = m_surfaceFormat.colorSpace;
    m_createInfo.imageExtent = extent;
    m_createInfo.imageArrayLayers = m_imageArrayLayers;
    m_createInfo.imageUsage = m_imageUsage;
    m_createInfo.imageSharingMode = m_imageSharingMode;
    m_createInfo.queueFamilyIndexCount = m_queueFamilyIndexCount;
    m_createInfo.pQueueFamilyIndices = m_pQueueFamilyIndices;
    m_createInfo.preTransform = m_preTransform;
    m_createInfo.compositeAlpha = m_compositeAlpha;
    m_createInfo.presentMode = m_presentMode;
    m_createInfo.clipped = m_clipped;
    m_createInfo.oldSwapchain = m_oldSwapchain;

    // create vulkan object
    m_created = Utilities::checkVKCreation(vkCreateSwapchainKHR(m_device,
                                                               &m_createInfo,
                                                                nullptr,
                                                               &m_swapChain));

    // create swap chain images
    createImageViews(m_imageCount);
    return m_created;
}

std::vector<VkImageView> SwapChain::imageViews()
{
    std::vector<VkImageView> swapChainImageViews;
    swapChainImageViews.resize(m_swapChainImageViews.size());
    for (int i=0; i<m_swapChainImageViews.size(); i++)
    {
        swapChainImageViews[i] = m_swapChainImageViews[i]->view();
    }
    return swapChainImageViews;
}

VkExtent2D SwapChain::extent()
{
    return m_extent;
}

VkFormat SwapChain::format()
{
    return m_surfaceFormat.format;
}

VkSwapchainKHR SwapChain::buffer()
{
    return m_swapChain;
}

std::vector<VkFramebuffer> SwapChain::framebuffers()
{
    return m_swapChainFramebuffers;
}

bool SwapChain::createFrameBuffers(VkRenderPass renderPass)
{
    // create swap chain frame buffers associated with each image view
    m_swapChainFramebuffers.resize(m_swapChainImageViews.size());

    // The attachments specified during render pass creation are bound by wrapping them into
    // a VkFramebuffer object. A framebuffer object references all of the VkImageView objects
    // that represent the attachments. 
    for (size_t i = 0; i < m_swapChainImageViews.size(); i++)
    {
        // the image that we have to use for the attachment depends on which image the swap chain
        // returns when we retrieve one for presentation. That means that we have to create a framebuffer
        // for all of the images in the swap chain and use the one that corresponds to the retrieved
        // image at drawing time.
        std::array<VkImageView, 2> attachments = {
            m_swapChainImageViews[i]->view(),
            m_depthImageView->view()
        };
        
        VkFramebufferCreateInfo framebufferInfo{};
        framebufferInfo.sType = VK_STRUCTURE_TYPE_FRAMEBUFFER_CREATE_INFO;
        framebufferInfo.pNext = m_pNext;
        framebufferInfo.flags = m_flags;

        // need to specify with which renderPass the framebuffer needs to be compatible. You can only
        // use a framebuffer with the render passes that it is compatible with, which roughly means that
        // they use the same number and type of attachments.
        framebufferInfo.renderPass = renderPass;

        // The attachmentCount and pAttachments parameters specify the VkImageView objects that should
        // be bound to the respective attachment descriptions in the render pass pAttachment array.
        framebufferInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
        framebufferInfo.pAttachments = attachments.data();

        // The width and height parameters are self-explanatory and layers refers to the number of layers
        // in image arrays. Our swap chain images are single images, so the number of layers is 1.
        framebufferInfo.width = m_extent.width;
        framebufferInfo.height = m_extent.height;
        framebufferInfo.layers = 1;

        // create vulkan object
        return Utilities::checkVKCreation(vkCreateFramebuffer(m_device,
                                                            &framebufferInfo,
                                                             nullptr,
                                                            &m_swapChainFramebuffers[i]));
    }
}

void SwapChain::createImageViews(uint32_t imageCount)
{
    // create depth image
    VkExtent3D imageExtent;
    imageExtent.width = m_extent.width;
    imageExtent.height = m_extent.height;
    imageExtent.depth = 1;
    m_depthImage = new Image(m_device, m_depthFormat, imageExtent, m_mipLevels, m_tiling, VK_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, m_memoryProperties);
    m_depthImageView = new ImageView(m_device, m_depthImage->image(), m_depthFormat, VK_IMAGE_ASPECT_DEPTH_BIT, m_mipLevels);

    // create MSAA color image
    // m_colorImageView = new ImageView(m_device);

    // create main swap chain images
    vkGetSwapchainImagesKHR(m_device, m_swapChain, &imageCount, nullptr);
    m_swapChainImages.resize(imageCount);
    vkGetSwapchainImagesKHR(m_device, m_swapChain, &imageCount, m_swapChainImages.data());
    m_swapChainImageViews.resize(m_swapChainImages.size());
    for (size_t i = 0; i < m_swapChainImages.size(); i++) 
    {
        m_swapChainImageViews[i] = new ImageView(m_device, m_swapChainImages[i], m_surfaceFormat.format, VK_IMAGE_ASPECT_COLOR_BIT, m_mipLevels);
    }
}

VkSurfaceFormatKHR SwapChain::selectSwapSurfaceFormat(const std::vector<VkSurfaceFormatKHR>& availableFormats) 
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

VkPresentModeKHR SwapChain::selectSwapPresentMode(const std::vector<VkPresentModeKHR>& availablePresentModes) 
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

VkExtent2D SwapChain::selectSwapExtent(const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent)
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
    if(capabilities.currentExtent.width != std::numeric_limits<uint32_t>::max())
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
