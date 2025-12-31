/**
 * @file
 * @brief
 * @author
 * @note
 */

#include "Buffer.h"
#include "Utility/VulkanUtil.h"

using namespace VulkanEngine;

Buffer::Buffer()
    : m_sType(0)
    , m_pNext(NULL)
    , m_flags(0)
    , m_size(0)
    , m_usage(0)
    , m_sharingMode(0)
    , m_queueFamilyIndexCount(0)
    , m_pQueueFamilyIndices(0)
    , m_memoryRequirements(0)
    , m_buffer(VK_NULL_HANDLE)
    , m_memory(VK_NULL_HANDLE)
    , m_logicalDevice(VK_NULL_HANDLE)
{
    m_logger = VulkanLogger::Instance();
}

Buffer::~Buffer()
{

}

void Buffer::initialize(VkDevice logicalDevice, VkMemoryRequirements memoryRequirements)
{
    m_logicalDevice = logicalDevice;
    m_memoryRequirements = memoryRequirements;
}

void Buffer::createBuffer(VkBufferCreateInfo bufferInfo, VkBuffer& buffer)
{
    VulkanUtil::checkVKCreation(vkCreateBuffer(m_logicalDevice,
                                                 &bufferInfo,
                                                  nullptr, 
                                                 &buffer),
                                                  m_logger);
}

VkBuffer Buffer::allocate()
{
    m_allocInfo.sType = m_sType_alloc;
    m_allocInfo.allocationSize = m_allocationSize;
    m_allocInfo.memoryTypeIndex = m_memoryTypeIndex;
    VulkanUtil::checkVKCreation(vkAllocateMemory(m_logicalDevice, 
                                                &m_allocInfo, 
                                                 nullptr, 
                                                &m_memory),
                                                 m_logger);

    // If memory allocation was successful, then we can 
    // now associate this memory
    vkBindBufferMemory(m_logicalDevice, m_buffer, m_memory, 0);
    return m_memory;
}

uint32_t Buffer::findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties)
{
    for (uint32_t i = 0; i < m_memoryRequirements.memoryTypeCount; i++) 
    {
        if ((typeFilter & (1 << i)) && (m_memoryRequirements.memoryTypes[i].propertyFlags & properties) == properties) 
        {
            return i;
        }
    }
}