/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */

#include "SwapChain.h"

using namespace VulkanEngine;

VertexBuffer::VertexBuffer()
{}

VertexBuffer::~VertexBuffer()
{
    vkDestroyBuffer(m_device, m_buffer, nullptr);
}

bool VertexBuffer::create()
{
    // populate vulkan object creation info
    m_bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    m_bufferInfo.size = sizeof(vertices[0]) * vertices.size();
    m_bufferInfo.usage = VK_BUFFER_USAGE_VERTEX_BUFFER_BIT;
    m_bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    // create vulkan object
     createBuffer(m_bufferInfo, m_buffer);
}



