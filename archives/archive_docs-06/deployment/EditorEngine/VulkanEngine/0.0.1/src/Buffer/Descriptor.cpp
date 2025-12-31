/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Descriptor.h"
#include "Logger.h"
#include "VulkanCommon.h"
#include "VulkanConstants.h"
#include "Buffer/UniformBuffer.h"

using namespace RenderEngine;

Descriptor::Descriptor(VkDevice device)
    : m_device(device)
    , m_descriptorPool(VK_NULL_HANDLE)
    , m_descriptorSetLayout(VK_NULL_HANDLE)
    , m_maxPoolSize(10)
{
    create();
}

Descriptor::~Descriptor()
{}

void Descriptor::create()
{
    // camera
    VkDescriptorSetLayoutBinding cameraBinding{};
    cameraBinding.binding = 0;
    cameraBinding.descriptorCount = 1;
    cameraBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    cameraBinding.pImmutableSamplers = nullptr;
    cameraBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT | VK_SHADER_STAGE_FRAGMENT_BIT;

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
    Utilities::checkVKCreation(vkCreateDescriptorSetLayout(m_device,
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
    // poolSize.descriptorCount = static_cast<uint32_t>(Constants::MAX_FRAMES_IN_FLIGHT) * bindingCount;

    VkDescriptorPoolCreateInfo poolInfo{};
    poolInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
    poolInfo.flags = 0;
    poolInfo.maxSets = m_maxPoolSize;
    poolInfo.poolSizeCount =  (uint32_t)poolSizes.size();
    poolInfo.pPoolSizes = poolSizes.data();
    poolInfo.maxSets = static_cast<uint32_t>(Constants::MAX_FRAMES_IN_FLIGHT);

    // create vulkan object
    Utilities::checkVKCreation(vkCreateDescriptorPool(m_device,
                                                     &poolInfo,
                                                      nullptr,
                                                     &m_descriptorPool));

    std::vector<VkDescriptorSetLayout> layouts(Constants::MAX_FRAMES_IN_FLIGHT, m_descriptorSetLayout);
    VkDescriptorSetAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    allocInfo.descriptorPool = m_descriptorPool;
    allocInfo.descriptorSetCount = static_cast<uint32_t>(Constants::MAX_FRAMES_IN_FLIGHT);
    allocInfo.pSetLayouts = layouts.data();

    m_descriptorSets.resize(Constants::MAX_FRAMES_IN_FLIGHT);
    // create vulkan object
    Utilities::checkVKCreation(vkAllocateDescriptorSets(m_device,
                                                       &allocInfo,
                                                        m_descriptorSets.data()));
}

void Descriptor::updateDescriptorSets(std::vector<std::vector<UniformBuffer*>> uniformBuffers)
{
    for (auto ubo : uniformBuffers)
    {
        for (size_t i = 0; i < Constants::MAX_FRAMES_IN_FLIGHT; i++)
        {
            VkDescriptorBufferInfo bufferInfo{};
            bufferInfo.buffer = ubo[i]->buffer();
            bufferInfo.offset = 0;
            bufferInfo.range = ubo[i]->size();

            VkWriteDescriptorSet descriptorWrite{};
            descriptorWrite.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
            descriptorWrite.dstSet = m_descriptorSets[i];
            descriptorWrite.dstBinding = ubo[i]->binding();
            descriptorWrite.dstArrayElement = 0;
            descriptorWrite.descriptorType = ubo[i]->type();
            descriptorWrite.descriptorCount = 1;
            descriptorWrite.pBufferInfo = &bufferInfo;

            vkUpdateDescriptorSets(m_device, 1, &descriptorWrite, 0, nullptr);
        }
    }
}

std::vector<VkDescriptorSet> Descriptor::sets()
{
    return m_descriptorSets;
}

VkDescriptorSetLayout Descriptor::layout()
{
    return m_descriptorSetLayout;
}