/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Image.h"
#include "Logger.h"
#include "VulkanCommon.h"

using namespace RenderEngine;

Image::Image()
{}

Image::Image(VkDevice device, VkFormat format, VkExtent3D extent, uint32_t mipLevels, VkImageTiling tiling, VkImageUsageFlags usage, VkMemoryPropertyFlags memoryProperties, VkPhysicalDeviceMemoryProperties deviceMemoryProperties)
    : m_device(device)
    , m_image(VK_NULL_HANDLE)
    , m_imageInfo({})
    , m_allocInfo({})
    , m_sType(VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_imageType(VK_IMAGE_TYPE_2D)
    , m_format(format)
    , m_extent(extent)
    , m_mipLevels(mipLevels)
    , m_arrayLayers(1)
    , m_samples(VK_SAMPLE_COUNT_1_BIT)
    , m_tiling(tiling)
    , m_queueFamilyIndexCount(0)
    , m_usage(usage)
    , m_sharingMode(VK_SHARING_MODE_EXCLUSIVE)
    , m_pQueueFamilyIndices(NULL)
    , m_initialLayout(VK_IMAGE_LAYOUT_UNDEFINED)
    , m_memoryProperties(memoryProperties)
    , m_deviceMemoryProperties(deviceMemoryProperties)
    , m_memoryTypeIndex(0)
{
    create();
}

Image::~Image()
{}

VkImage Image::image()
{
    return m_image;
}

void Image::create()
{
    m_imageInfo.sType = m_sType;
    m_imageInfo.pNext = m_pNext;
    m_imageInfo.flags = m_flags;
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
    Utilities::checkVKCreation(vkCreateImage(m_device,
                                            &m_imageInfo,
                                             nullptr,
                                            &m_image));

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
    Utilities::checkVKCreation(vkAllocateMemory(m_device,
                                                &m_allocInfo,
                                                    nullptr,
                                                &m_imageMemory));
    vkBindImageMemory(m_device, m_image, m_imageMemory, 0);
}
