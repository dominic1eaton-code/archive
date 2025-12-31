/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "VertexBuffer.h"
#include "Logger.h"
#include "VulkanCommon.h"

using namespace RenderEngine;

VertexBuffer::VertexBuffer()
{}

VertexBuffer::VertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties)
    : Buffer(device, memoryProperties, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT)
{}

VertexBuffer::VertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size)
    : Buffer(device, memoryProperties, size, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT)
{}

VertexBuffer::~VertexBuffer()
{}
