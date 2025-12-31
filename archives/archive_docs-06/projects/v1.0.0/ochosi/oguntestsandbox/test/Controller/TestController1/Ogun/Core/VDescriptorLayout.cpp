/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VDescriptorLayout.h"
#include "VConstants.h"

using namespace ogun;


VDescriptorLayout& VDescriptorLayout::device(VkDevice device)
{
    m_device = device;
    return *this;
}

VDescriptorLayout& VDescriptorLayout::build()
{
    VkDescriptorSetLayoutBinding cameraBinding{};
    cameraBinding.binding = 0;
    cameraBinding.descriptorCount = 1;
    cameraBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    cameraBinding.pImmutableSamplers = nullptr;
    cameraBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;
    // cameraBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT | VK_SHADER_STAGE_FRAGMENT_BIT;

    VkDescriptorSetLayoutBinding meshBinding{};
    meshBinding.binding = 1;
    meshBinding.descriptorCount = 1;
    meshBinding.descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    meshBinding.pImmutableSamplers = nullptr;
    meshBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;

    VkDescriptorSetLayoutBinding textureBinding{};
    textureBinding.binding = 1;
    textureBinding.descriptorCount = 1;
    textureBinding.descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
    textureBinding.pImmutableSamplers = nullptr;
    textureBinding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    std::vector<VkDescriptorSetLayoutBinding> uboLayoutBindings;
    uboLayoutBindings.push_back(cameraBinding);
    uboLayoutBindings.push_back(meshBinding);
    uboLayoutBindings.push_back(textureBinding);

    // descriptor layout
    VkDescriptorSetLayoutCreateInfo layoutInfo{};
    layoutInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
	layoutInfo.flags = 0;
	layoutInfo.pNext = nullptr;
    layoutInfo.bindingCount = uboLayoutBindings.size();
    layoutInfo.pBindings = uboLayoutBindings.data();

    // create vulkan object
    createvk(vkCreateDescriptorSetLayout(m_device,
                                        &layoutInfo,
                                        nullptr,
                                        &m_descriptorSetLayout));

    // std::vector<VkDescriptorPoolSize> poolSizes =
    // {
    //     {VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER,         m_maxPoolSize},
    //     {VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER_DYNAMIC, m_maxPoolSize},
    //     {VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,         m_maxPoolSize}
    // };
    // // VkDescriptorPoolSize poolSize{};
    // // poolSize.type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    // // poolSize.descriptorCount = static_cast<uint32_t>(constants::MAX_FRAMES_IN_FLIGHT) * bindingCount;

    // VkDescriptorPoolCreateInfo poolInfo{};
    // poolInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
	// poolInfo.flags = 0;
	// poolInfo.maxSets = m_maxPoolSize;
    // poolInfo.poolSizeCount =  (uint32_t)poolSizes.size();
    // poolInfo.pPoolSizes = poolSizes.data();
    // poolInfo.maxSets = static_cast<uint32_t>(constants::MAX_FRAMES_IN_FLIGHT);

    // // create vulkan object
    // createvk(vkCreateDescriptorPool(m_device,
    //                                 &poolInfo,
    //                                 nullptr,
    //                                 &m_descriptorPool));

    // std::vector<VkDescriptorSetLayout> layouts(constants::MAX_FRAMES_IN_FLIGHT, m_descriptorSetLayout);
    // VkDescriptorSetAllocateInfo allocInfo{};
    // allocInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    // allocInfo.descriptorPool = m_descriptorPool;
    // allocInfo.descriptorSetCount = static_cast<uint32_t>(constants::MAX_FRAMES_IN_FLIGHT);
    // allocInfo.pSetLayouts = layouts.data();

    // m_descriptorSets.resize(constants::MAX_FRAMES_IN_FLIGHT);
    // createvk(vkAllocateDescriptorSets(m_device,
    //                                 &allocInfo,
    //                                 m_descriptorSets.data()));

    return *this;
}
