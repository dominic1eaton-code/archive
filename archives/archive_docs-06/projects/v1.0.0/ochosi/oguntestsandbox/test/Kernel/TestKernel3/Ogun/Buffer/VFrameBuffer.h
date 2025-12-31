/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VFrameBuffer_h
#define VFrameBuffer_h

#include "Ogun/Core/VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VFrameBuffer : public VObject<VFrameBuffer>
{
public:
    VFrameBuffer();
    
    virtual ~VFrameBuffer(void) = default;
    
    VFrameBuffer& device(VkDevice device);

    VFrameBuffer& build(VkRenderPass renderPass);

private:

    VkDevice m_device;

    VkFramebuffer m_buffer;

    
    VkFramebufferCreateInfo m_framebufferInfo{};

};

} // namespace ogun

#endif // VFrameBuffer_h