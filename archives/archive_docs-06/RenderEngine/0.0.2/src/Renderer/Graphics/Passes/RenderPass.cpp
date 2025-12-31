/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */

using namespace RenderEngine;

RenderPass::RenderPass()
{}

RenderPass::~RenderPass()
{}



v000oid RenderPass::begin(uint32_t imageIndex)
{
    // Drawing starts by beginning the render pass
    m_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;

    // The first parameters are the render pass itself and the attachments to bind. We created
    // a framebuffer for each swap chain image where it is specified as a color attachment. Thus
    // we need to bind the framebuffer for the swapchain image we want to draw to. Using the
    // imageIndex parameter which was passed in, we can pick the right framebuffer for the
    // current swapchain image.
    m_renderPassInfo.renderPass = m_renderPass;
    m_renderPassInfo.framebuffer = m_swapChainFramebuffers[imageIndex];

    // define the size of the render area. The render area defines where shader loads and stores will
    // take place. The pixels outside this region will have undefined values. It should match the size
    // of the attachments for best performance
    m_renderPassInfo.renderArea.offset = {0, 0};
    m_renderPassInfo.renderArea.extent = m_swapChainExtent;

    // The last two parameters define the clear values to use for VK_ATTACHMENT_LOAD_OP_CLEAR, which we
    // used as load operation for the color attachment. I've defined the clear color to simply be black
    // with 100% opacity.
    std::array<VkClearValue, 2> clearValues{};
    clearValues[0].color = {{0.0f, 0.0f, 0.0f, 1.0f}};
    clearValues[1].depthStencil = {1.0f, 0};
    m_renderPassInfo.clearValueCount = static_cast<uint32_t>(clearValues.size());
    m_renderPassInfo.pClearValues = clearValues.data();

    // The first parameter for every command is always the command buffer to record the command to. The
    // second parameter specifies the details of the render pass we've just provided. The final parameter
    // controls how the drawing commands within the render pass will be provided. It can have one of two values:
    //     VK_SUBPASS_CONTENTS_INLINE                   : The render pass commands will be embedded in the
    //                                                    primary command buffer itself and no secondary command
    //                                                    buffers will be executed.
    //     VK_SUBPASS_CONTENTS_SECONDARY_COMMAND_BUFFERS: The render pass commands will be executed from secondary
    //                                                    command buffers.
    vkCmdBeginRenderPass(m_cmd, &m_renderPassInfo, m_subpassContents);
}

void RenderPass::end()
{
    vkCmdEndRenderPass(m_cmd);
}

void RenderPass::draw()
{
    objectBuffer[imageIndex]->map();
    
    for (int rObj = 0; rObj < ssbo.size(); rObj++) 
    {

    }

    objectBuffer[imageIndex]->unmap();

}