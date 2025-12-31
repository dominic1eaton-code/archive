/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VPass_h
#define VPass_h

#include "VObject.h"
#include <vector>

namespace ogun
{

class VPass : public VObject<VPass>
{
public:
    VPass();

    virtual ~VPass(void) = default;

    void execute();

    void begin(VkRect2D renderArea, std::array<VkClearValue, 2> clearValues, VkFramebuffer framebuffer);

    void end();

    void pass();

private:

    VkRenderPassBeginInfo m_renderPassInfo;

};

} // namespace ogun

#endif // VPass_h