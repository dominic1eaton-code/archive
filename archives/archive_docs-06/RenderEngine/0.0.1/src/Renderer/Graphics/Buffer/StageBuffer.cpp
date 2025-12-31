/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "StageBuffer.h"
#include "Logger.h"
#include "VulkanCommon.h"

using namespace RenderEngine;

StageBuffer::StageBuffer()
{}

StageBuffer::StageBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties)
    : Buffer(device, memoryProperties, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)
{}

StageBuffer::StageBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size)
    : Buffer(device, memoryProperties, size, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)
{}

StageBuffer::~StageBuffer()
{}

void StageBuffer::map(const std::vector<Vertex> vertices)
{
    void* data;
    vkMapMemory(m_device, m_bufferMemory, 0, m_size, 0, &data);
    memcpy(data, vertices.data(), (size_t) m_size);
    vkUnmapMemory(m_device, m_bufferMemory);
}

void StageBuffer::map(std::vector<uint16_t> indices)
{
    void* data;
    vkMapMemory(m_device, m_bufferMemory, 0, m_size, 0, &data);
    memcpy(data, indices.data(), (size_t) m_size);
    vkUnmapMemory(m_device, m_bufferMemory);
}
