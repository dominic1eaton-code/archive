/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VVertexBuffer_h
#define VVertexBuffer_h

#include "Ogun/Core/VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VVertexBuffer : public VObject<VVertexBuffer>
{
public:
    VVertexBuffer();
    
    virtual ~VVertexBuffer(void) = default;

    VertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties);

    VertexBuffer(VkDevice device, VkPhysicalDeviceMemoryProperties memoryProperties, VkDeviceSize size);
    
    virtual ~VertexBuffer(void);

    /* */
    void map() {};

    /* */
    void map(const std::vector<Vertex> vertices) {};

    /* */
    void map(std::vector<uint16_t> indices) {};


};

} // namespace ogun

#endif // VVertexBuffer_h