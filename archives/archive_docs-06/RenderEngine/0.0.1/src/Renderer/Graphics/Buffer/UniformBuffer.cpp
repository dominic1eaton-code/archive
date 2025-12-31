/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "UniformBuffer.h"
#include "Logger.h"
#include "VulkanCommon.h"
#include "Buffer/UniformBufferObject.h"

using namespace RenderEngine;

UniformBuffer::UniformBuffer()
{}

UniformBuffer::UniformBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDescriptorType type, uint32_t binding)
    : Buffer(device, memoryProperties, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)
    , m_type(type)
    , m_binding(binding)
{}

UniformBuffer::UniformBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDescriptorType type, uint32_t binding, VkBufferUsageFlags usage)
    : Buffer(device, memoryProperties, usage, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)
    , m_type(type)
    , m_binding(binding)
{}

UniformBuffer::UniformBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size)
    : Buffer(device, memoryProperties, size, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)
{}

UniformBuffer::~UniformBuffer()
{}
  
VkDescriptorType UniformBuffer::type()
{
    return m_type;
}
  
uint32_t UniformBuffer::binding()
{
    return m_binding;
}


void UniformBuffer::map()
{
    vkMapMemory(m_device, m_bufferMemory, 0, m_size, 0, &m_buffersMapped);
}

void UniformBuffer::copy(UniformBufferObject ubo)
{
    memcpy(m_buffersMapped, &ubo, sizeof(ubo));
}

void* UniformBuffer::buffersMapped()
{
    return m_buffersMapped;
}
