/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VDescriptorLayout_h
#define VDescriptorLayout_h

#include "VObject.h"
#include <vector>
#include <string>

namespace ogun
{
class UniformBuffer;

class VDescriptorLayout : public VObject<VDescriptorLayout>
{
public:
    VDescriptorLayout() = default;

    VDescriptorLayout(std::string filename);

    VDescriptorLayout& device(VkDevice device);

    VDescriptorLayout& build();
    
    VkDescriptorSetLayout layout() const { return m_descriptorSetLayout; }

private:

    VkDevice m_device;
    
    VkDescriptorSetLayout m_descriptorSetLayout;
    
    /* */
    uint32_t m_maxPoolSize;

    /* */
    std::vector<UniformBuffer*> m_uniformBuffers;

    /* */
    VkDeviceSize m_bufferSize;

    /* */
    std::vector<VkDescriptorSet> m_descriptorSets;

    /* */
    VkDescriptorPool m_descriptorPool;

    /* */
    VkImage m_textureImage;

    /* */
    VkDeviceMemory m_textureImageMemory;

    /* */
    VkImageView m_textureImageView;

    /* */
    VkSampler m_textureSampler;

};

} // namespace ogun

#endif // VDescriptorLayout_h