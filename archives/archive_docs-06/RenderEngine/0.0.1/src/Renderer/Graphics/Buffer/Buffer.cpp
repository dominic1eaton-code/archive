/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Buffer.h"
#include "Logger.h"
#include "VulkanCommon.h"

using namespace RenderEngine;

Buffer::Buffer()
    : m_sType(VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_sharingMode(VK_SHARING_MODE_EXCLUSIVE)
    , m_bufferInfo({})
    , m_bufferMemory(VK_NULL_HANDLE)
    , m_allocInfo({})
    , m_properties(VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT)
{}

Buffer::Buffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties)
    : m_device(device)
    , m_sType(VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_sharingMode(VK_SHARING_MODE_EXCLUSIVE)
    , m_bufferInfo({})
    , m_bufferMemory(VK_NULL_HANDLE)
    , m_allocInfo({})
    , m_memoryProperties(memoryProperties)
    , m_size(size)
    , m_usage(usage)
    , m_properties(properties)
{}

Buffer::Buffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties)
    : m_device(device)
    , m_sType(VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_sharingMode(VK_SHARING_MODE_EXCLUSIVE)
    , m_bufferInfo({})
    , m_bufferMemory(VK_NULL_HANDLE)
    , m_allocInfo({})
    , m_memoryProperties(memoryProperties)
    , m_usage(usage)
    , m_properties(properties)
{}

Buffer::~Buffer()
{
    deallocate();
}

void Buffer::create()
{
    m_bufferInfo.sType = m_sType;
    m_bufferInfo.size = m_size;
    m_bufferInfo.usage = m_usage;
    m_bufferInfo.sharingMode = m_sharingMode;

    // create vulkan object
    Utilities::checkVKCreation(vkCreateBuffer(m_device,
                                             &m_bufferInfo,
                                              nullptr,
                                             &m_buffer));

    // The buffer has been created, but it doesn't actually have any memory
    // assigned to it yet. The first step of allocating memory for the buffer
    // is to query its memory requirements 
    // The VkMemoryRequirements struct has three fields:
    //     size          : The size of the required amount of memory in bytes, may differ from bufferInfo.size.
    //     alignment     : The offset in bytes where the buffer begins in the allocated region of memory, depends on bufferInfo.usage and bufferInfo.flags.
    //     memoryTypeBits: Bit field of the memory types that are suitable for the buffer.
    vkGetBufferMemoryRequirements(m_device, m_buffer, &m_memoryRequirements);

    // We now have a way to determine the right memory type, so we can actually allocate the memory
    m_allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    m_allocInfo.allocationSize = m_memoryRequirements.size;
    m_allocInfo.memoryTypeIndex = findMemoryType(m_memoryRequirements.memoryTypeBits, m_properties);

    // Memory allocation is now as simple as specifying the size and type, both of which are
    // derived from the memory requirements of the vertex buffer and the desired property.
    Utilities::checkVKCreation(vkAllocateMemory(m_device,
                                               &m_allocInfo,
                                                nullptr,
                                               &m_bufferMemory));

    // If memory allocation was successful, then we can now associate this memory with the buffer using. The fourth parameter
    // is the offset within the region of memory. Since this memory is allocated specifically for this the vertex buffer, the
    // offset is simply 0. If the offset is non-zero, then it is required to be divisible by m_memoryProperties.alignment.
    vkBindBufferMemory(m_device, m_buffer, m_bufferMemory, 0);
}

uint32_t Buffer::findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties)
{
    for (uint32_t i = 0; i < m_memoryProperties.memoryTypeCount; i++)
    {
        if ((typeFilter & (1 << i)) && (m_memoryProperties.memoryTypes[i].propertyFlags & properties) == properties)
        {
            return i;
        }
    }
    throw std::runtime_error("failed to find suitable memory type!");
}

VkDeviceSize Buffer::size()
{
    return m_size;
}

void Buffer::allocate(VkDeviceSize size)
{
    m_size = size;
    create();
}

void Buffer::deallocate()
{
    vkDestroyBuffer(m_device, m_buffer, nullptr);
    vkFreeMemory(m_device, m_bufferMemory, nullptr);
}

VkBuffer Buffer::buffer()
{
    return m_buffer;
}

void Buffer::unmap()
{
    vkUnmapMemory(m_device, m_bufferMemory);
}
