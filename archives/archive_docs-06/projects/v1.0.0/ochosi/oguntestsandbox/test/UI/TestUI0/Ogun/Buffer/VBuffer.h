/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VBuffer_h
#define VBuffer_h

#include "Ogun/Core/VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VBuffer : public VObject<VBuffer>
{
public:
    Buffer();
   
    Buffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties);
   
    Buffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties);
   
    virtual ~Buffer(void);

    /* */
    void allocate(VkDeviceSize size);

    /* */
    VkBuffer buffer();

    /* */
    VkDeviceSize size();

    /* */
    void deallocate();

    /* */
    void unmap();

protected:

    /* */
    void build();

    /* */
    uint32_t findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties);

    /* */
    virtual void map() = 0;

    /* */
    virtual void map(const std::vector<Vertex> vertices) = 0;

    /* */
    virtual void map(std::vector<uint16_t> indices) = 0;


    /* */
    VkDeviceSize m_size;

    /* */
    VkBufferUsageFlags m_usage;

    /* */
    VkMemoryPropertyFlags m_properties;

    /* creation type */
    VkStructureType m_sType;

    /* Pointer to extension structure */
    const void* m_pNext;

    /* instance creation flags */
    VkInstanceCreateFlags m_flags;

    /* */
    VkSharingMode m_sharingMode;

    /* */
    VkDevice m_device;

    /* */
    VkBuffer m_buffer;

    /* */
    VkBufferCreateInfo m_bufferInfo;

    /* */
    VkDeviceMemory m_bufferMemory;

    /* */
    VkMemoryAllocateInfo m_allocInfo;

    /* */
    VkMemoryRequirements m_memoryRequirements;

    /* */
    VkPhysicalDeviceMemoryProperties m_memoryProperties;

};

} // namespace ogun

#endif // VBuffer_h