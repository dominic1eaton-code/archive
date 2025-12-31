/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "ImageView.h"
#include "Logger.h"
#include "VulkanCommon.h"


using namespace RenderEngine;

ImageView::ImageView()
{}

ImageView::ImageView(VkDevice device, VkImage image, VkFormat format, VkImageAspectFlags aspectFlags, uint32_t mipLevels)
    : m_device(device)
    , m_view(VK_NULL_HANDLE)
    , m_createInfo({})
    , m_sType(VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_image(image)
    , m_viewType(VK_IMAGE_VIEW_TYPE_2D)
    , m_format(format)
    , m_aspectFlags(aspectFlags)
    , m_components({VK_COMPONENT_SWIZZLE_IDENTITY, VK_COMPONENT_SWIZZLE_IDENTITY, VK_COMPONENT_SWIZZLE_IDENTITY, VK_COMPONENT_SWIZZLE_IDENTITY})
    , m_mipLevels(mipLevels)
{
    create();
}

ImageView::~ImageView()
{}

VkImageView ImageView::view()
{
    return m_view;
}

void ImageView::create()
{
    m_createInfo.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
    m_createInfo.image = m_image;

    // The viewType parameter allows you to treat images as 
    // 1D textures, 2D textures, 3D textures and cube maps
    m_createInfo.viewType = m_viewType;
    m_createInfo.format = m_format;

    // The components field allows you to swizzle the color channels around.
    // For example, you can map all of the channels to the red channel for a
    // monochrome texture. You can also map constant values of 0 and 1 to a
    // channel. In our case we'll stick to the default mapping
    m_createInfo.components.r = m_components.r;
    m_createInfo.components.g = m_components.g;
    m_createInfo.components.b = m_components.b;
    m_createInfo.components.a = m_components.a;

    // The subresourceRange field describes what the image's purpose is and which
    // part of the image should be accessed. Our images will be used as color targets
    // without any mipmapping levels or multiple layers.
    m_createInfo.subresourceRange.aspectMask = m_aspectFlags;
    m_createInfo.subresourceRange.baseMipLevel = 0;
    m_createInfo.subresourceRange.levelCount = m_mipLevels;
    m_createInfo.subresourceRange.baseArrayLayer = 0;
    m_createInfo.subresourceRange.layerCount = 1;

    // create vulkan object
    Utilities::checkVKCreation(vkCreateImageView(m_device,
                                                &m_createInfo,
                                                 nullptr,
                                                &m_view));
}
