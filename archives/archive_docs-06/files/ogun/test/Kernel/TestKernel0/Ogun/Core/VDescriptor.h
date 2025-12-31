/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VDescriptor_h
#define VDescriptor_h

#include "VObject.h"
#include <vector>
#include <string>

namespace ogun
{
class UniformBuffer;

class VDescriptor : public VObject<VDescriptor>
{
public:
    VDescriptor() = default;

    VDescriptor(std::string filename);

    VDescriptor& device(VkDevice device);

    VDescriptor& build();
    
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

#endif // VDescriptor_h