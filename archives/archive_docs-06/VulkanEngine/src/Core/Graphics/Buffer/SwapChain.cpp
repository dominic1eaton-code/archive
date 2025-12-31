/**
 * @copyright DEFAULT
 * @brief: Swapchain will own frame buffers that will be
 *         presented to screen. Queue of images that are
 *         waiting to be presented to the screen
 * @note : N/A
 */

#include "SwapChain.h"

using namespace VulkanEngine;

SwapChain::SwapChain()
{}

SwapChain::~SwapChain() {}

bool SwapChain::create()
{
    // populate vulkan object creation info
    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.surface = m_window->surface();
    m_createInfo.minImageCount = m_imageCount;
    m_createInfo.imageFormat = m_swapChainSurfaceFormat.format;
    m_createInfo.imageColorSpace = m_swapChainSurfaceFormat.colorSpace;
    m_createInfo.imageExtent = m_swapChainExtent;
    m_createInfo.imageArrayLayers = imageArrayLayers;
    m_createInfo.imageUsage = m_imageUsage;
    m_createInfo.imageSharingMode = m_imageSharingMode;
    m_createInfo.queueFamilyIndexCount = m_queueFamilyIndexCount;
    m_createInfo.pQueueFamilyIndices = m_pQueueFamilyIndices;
    m_createInfo.preTransform = swapChainSupport.capabilities.currentTransform;
    m_createInfo.compositeAlpha = m_compositeAlpha;
    m_createInfo.presentMode = m_swapChainPresentMode;
    m_createInfo.clipped = m_clipped;
    m_createInfo.oldSwapchain = m_oldSwapchain;

    // create vulkan object
    m_instance->createVKObject(vkCreateInstance(&m_createInfo, 
                                                  nullptr, 
                                                  &m_instance),
                                                  m_logger);

    // create images to be viewed on the swapchain
    createImages();

    // create image viewers to access images on swapchain
    createImageViews();
}



