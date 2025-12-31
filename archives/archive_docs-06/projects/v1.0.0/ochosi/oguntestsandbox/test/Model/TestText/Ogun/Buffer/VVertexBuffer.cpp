/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VVVertexBuffer.h"

using namespace ogun;

VVertexBuffer::VVertexBuffer()
{}

VVertexBuffer::VVertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties)
    : Buffer(device, memoryProperties, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT)
{}

VVertexBuffer::VVertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size)
    : Buffer(device, memoryProperties, size, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT)
{}

VVertexBuffer::~VVertexBuffer()
{}
