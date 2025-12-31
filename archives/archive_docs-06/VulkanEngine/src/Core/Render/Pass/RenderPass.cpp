/**
 * @file
 * @brief
 * @author
 * @note
 */

#include "RenderPass.h"
#include "VInstance.h"
#include "Utility/VulkanUtil.h"

using namespace VulkanEngine;

RenderPass::RenderPass()
{}

RenderPass::~RenderPass()
{

}

// put draw commands on execution buffer
void RenderPass::draw(VkCommandBuffer cmd)
{
    begin(cmd, rpInfo);
    render(cmd);
    end(cmd);
}

void RenderPass::begin(VkRenderPassBeginInfo rpInfo)
{
    vkCmdBeginRenderPass(cmd, &rpInfo, VK_SUBPASS_CONTENTS_INLINE);
}

void RenderPass::end(VkRenderPassBeginInfo rpInfo)
{
    vkCmdEndRenderPass(cmd);
}

