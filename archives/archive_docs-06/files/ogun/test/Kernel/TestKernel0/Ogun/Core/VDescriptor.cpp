/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VDescriptor.h"
#include "VConstants.h"

using namespace ogun;


VDescriptor& VDescriptor::device(VkDevice device)
{
    m_device = device;
    return *this;
}

VDescriptor& VDescriptor::build()
{
    // camera
    VkDescriptorSetLayoutBinding cameraBinding{};
    cameraBinding.binding = 0;
    cameraBinding.descriptorCount = 1;
    cameraBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    cameraBinding.pImmutableSamplers = nullptr;
    cameraBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;

    // Light
    VkDescriptorSetLayoutBinding lightBinding{};
    lightBinding.binding = 1;
    lightBinding.descriptorCount = 1;
    lightBinding.descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    lightBinding.pImmutableSamplers = nullptr;
    lightBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT | VK_SHADER_STAGE_FRAGMENT_BIT;

    // descriptor layout
    uint32_t bindingCount = 2;
    VkDescriptorSetLayoutBinding uboLayoutBindings[] = {cameraBinding, lightBinding};
    VkDescriptorSetLayoutCreateInfo layoutInfo{};
    layoutInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
	layoutInfo.flags = 0;
	layoutInfo.pNext = nullptr;
    layoutInfo.bindingCount = bindingCount;
    layoutInfo.pBindings = uboLayoutBindings;

    // create vulkan object
    createVk(vkCreateDescriptorSetLayout(m_device,
                                        &layoutInfo,
                                        nullptr,
                                        &m_descriptorSetLayout));

                                        
    std::vector<VkDescriptorPoolSize> poolSizes =
    {
        {VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER,         m_maxPoolSize},
        {VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER_DYNAMIC, m_maxPoolSize},
        {VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,         m_maxPoolSize}
    };
    // VkDescriptorPoolSize poolSize{};
    // poolSize.type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    // poolSize.descriptorCount = static_cast<uint32_t>(constants::MAX_FRAMES_IN_FLIGHT) * bindingCount;

    VkDescriptorPoolCreateInfo poolInfo{};
    poolInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
	poolInfo.flags = 0;
	poolInfo.maxSets = m_maxPoolSize;
    poolInfo.poolSizeCount =  (uint32_t)poolSizes.size();
    poolInfo.pPoolSizes = poolSizes.data();
    poolInfo.maxSets = static_cast<uint32_t>(constants::MAX_FRAMES_IN_FLIGHT);

    // create vulkan object
    createVk(vkCreateDescriptorPool(m_device,
                                    &poolInfo,
                                    nullptr,
                                    &m_descriptorPool));

    std::vector<VkDescriptorSetLayout> layouts(constants::MAX_FRAMES_IN_FLIGHT, m_descriptorSetLayout);
    VkDescriptorSetAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    allocInfo.descriptorPool = m_descriptorPool;
    allocInfo.descriptorSetCount = static_cast<uint32_t>(constants::MAX_FRAMES_IN_FLIGHT);
    allocInfo.pSetLayouts = layouts.data();

    m_descriptorSets.resize(constants::MAX_FRAMES_IN_FLIGHT);
    createVk(vkAllocateDescriptorSets(m_device,
                                    &allocInfo,
                                    m_descriptorSets.data()));

    return *this;
}
