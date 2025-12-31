/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VRenderPass_h
#define VRenderPass_h

#include "VObject.h"
#include <vector>

namespace ogun
{

class VRenderPass : public VObject<VRenderPass>
{
public:
    VRenderPass();
    virtual ~VRenderPass(void) = default;
    
    VkRenderPass pass() const { return m_renderPass; }

    VRenderPass& device(VkDevice device);
 
    VRenderPass& format(VkFormat format);

    VRenderPass& depth(VkFormat depth);
    
    VRenderPass& bindpoint(VkPipelineBindPoint bpoint);

    VRenderPass& samples(VkSampleCountFlagBits samples);

    VRenderPass& build();

private:
    VkSampleCountFlagBits m_msaaSamples;

    VkPipelineBindPoint m_pipelineBindPoint;

    /* */
    VkDevice m_device;
    
    /* */
    VkRenderPass m_renderPass;

    /* */
    VkRenderPassCreateInfo m_renderPassInfo;
    
    /* */
    VkFormat m_depthFormat;
    
    /* */
    VkFormat m_imageFormat;
};

} // namespace ogun

#endif // VRenderPass_h