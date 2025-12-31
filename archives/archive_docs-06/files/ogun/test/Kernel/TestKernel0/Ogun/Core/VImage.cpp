/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VImage.h"

using namespace ogun;


VImageView& VImageView::build()
{
    VkImageViewCreateInfo createInfo{};
    createInfo.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
    createInfo.image = m_swapChainImages[i];

    // The viewType parameter allows you to treat images as 
    // 1D textures, 2D textures, 3D textures and cube maps
    createInfo.viewType = VK_IMAGE_VIEW_TYPE_2D;
    createInfo.format = m_surfaceFormat.format;

    // The components field allows you to swizzle the color channels around.
    // For example, you can map all of the channels to the red channel for a
    // monochrome texture. You can also map constant values of 0 and 1 to a
    // channel. In our case we'll stick to the default mapping
    createInfo.components.r = VK_COMPONENT_SWIZZLE_IDENTITY;
    createInfo.components.g = VK_COMPONENT_SWIZZLE_IDENTITY;
    createInfo.components.b = VK_COMPONENT_SWIZZLE_IDENTITY;
    createInfo.components.a = VK_COMPONENT_SWIZZLE_IDENTITY;

    // The subresourceRange field describes what the image's purpose is and which
    // part of the image should be accessed. Our images will be used as color targets
    // without any mipmapping levels or multiple layers.
    createInfo.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    createInfo.subresourceRange.baseMipLevel = 0;
    createInfo.subresourceRange.levelCount = 1;
    createInfo.subresourceRange.baseArrayLayer = 0;
    createInfo.subresourceRange.layerCount = 1;

    // create vulkan object
    createVk(vkCreateImageView(m_device,
                                &createInfo,
                                    nullptr,
                                &m_swapChainImageViews[i]));
}


VImage& VImage::build()
{
    m_imageInfo.sType = VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO;
    m_imageInfo.pNext = NULL;
    m_imageInfo.flags = 0;
    m_imageInfo.imageType = m_imageType;
    m_imageInfo.extent.width = m_extent.width;
    m_imageInfo.extent.height = m_extent.height;
    m_imageInfo.extent.depth = m_extent.depth;
    m_imageInfo.mipLevels = m_mipLevels;
    m_imageInfo.arrayLayers = m_arrayLayers;
    m_imageInfo.format = m_format;
    m_imageInfo.tiling = m_tiling;
    m_imageInfo.initialLayout = m_initialLayout;
    m_imageInfo.usage = m_usage;
    m_imageInfo.samples = m_samples;
    m_imageInfo.sharingMode = m_sharingMode;

    // create vulkan object
    createVk(vkCreateImage(m_device,
                            &m_imageInfo,
                                nullptr,
                            &m_image));
    allocate();
    return *this;
}

void VImage::allocate()
{
    /* allocate image memory */
    VkMemoryRequirements memRequirements;
    vkGetImageMemoryRequirements(m_device, m_image, &memRequirements);
    for (uint32_t i = 0; i < m_deviceMemoryProperties.memoryTypeCount; i++)
    {
        if ((memRequirements.memoryTypeBits & (1 << i)) && (m_deviceMemoryProperties.memoryTypes[i].propertyFlags & m_memoryProperties) == m_memoryProperties)
        {
            m_memoryTypeIndex = i;
        }
    }

    m_allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    m_allocInfo.allocationSize = memRequirements.size;
    m_allocInfo.memoryTypeIndex = m_memoryTypeIndex;
    createVk(vkAllocateMemory(m_device,
                                &m_allocInfo,
                                    nullptr,
                                &m_imageMemory));
    vkBindImageMemory(m_device, m_image, m_imageMemory, 0);
}