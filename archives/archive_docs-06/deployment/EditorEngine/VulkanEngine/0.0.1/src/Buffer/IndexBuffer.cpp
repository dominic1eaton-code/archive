/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "IndexBuffer.h"
#include "Logger.h"
#include "VulkanCommon.h"

using namespace RenderEngine;

IndexBuffer::IndexBuffer()
{}

IndexBuffer::IndexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties)
    : Buffer(device, memoryProperties, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_INDEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT)
{}

IndexBuffer::IndexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size)
    : Buffer(device, memoryProperties, size, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_INDEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT)
{}

IndexBuffer::~IndexBuffer()
{}
