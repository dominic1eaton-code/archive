/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VImage_h
#define VImage_h

#include "VObject.h"
#include <vector>

namespace ogun
{

class VImageView : public VObject<VImageView>
{
public:
    VImageView();
    virtual ~VImageView(void) = default;

    VImageView& build();

};

class VImage : public VObject<VImage>
{
public:
    VImage();
    virtual ~VImage(void) = default;
    
    VImage& build();

private:
    void allocate();
    
    /* */
    VkImage m_image;

    /* */
    VkImageCreateInfo m_imageInfo;

    /* */
    VkMemoryAllocateInfo m_allocInfo;

    /* */
    VkDeviceMemory m_imageMemory;

    /* */
    VkDevice m_device;

    /* */
    uint32_t m_memoryTypeIndex;

    /* */
    VkImageType  m_imageType;
    
    /* */
    VkFormat m_format;
    
    /* */
    VkExtent3D m_extent;
    
    /* */
    uint32_t m_mipLevels;
    
    /* */
    uint32_t m_arrayLayers;
    
    /* */
    VkSampleCountFlagBits m_samples;
    
    /* */
    VkImageTiling m_tiling;
    
    /* */
    uint32_t m_queueFamilyIndexCount;
    
    /* */
    VkImageUsageFlags m_usage;
    
    /* */
    VkSharingMode m_sharingMode;
    
    /* */
    const uint32_t* m_pQueueFamilyIndices;
    
    /* */
    VkImageLayout m_initialLayout;
    
    /* */
    VkMemoryPropertyFlags m_memoryProperties;
    
    /* */
    VkPhysicalDeviceMemoryProperties m_deviceMemoryProperties;
};

} // namespace ogun

#endif // VImage_h