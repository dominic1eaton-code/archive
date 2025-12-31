/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VPass.h"
#include <string>
#include <array>

using namespace ogun;


void VPass::begin(VkRect2D renderArea, std::array<VkClearValue, 2> clearValues, VkFramebuffer framebuffer)
{
    m_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;
    m_renderPassInfo.pNext = NULL;
    m_renderPassInfo.renderPass = m_renderpass;
    m_renderPassInfo.framebuffer = framebuffer;
    m_renderPassInfo.renderArea = renderArea;
    m_renderPassInfo.clearValueCount = static_cast<uint32_t>(clearValues.size());;
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

void VPass::pass(std::vector<VRenderObject> objects)
{
    for (auto robj : objects)
    {
        allocate(robj);
        record(robj);
    }
}

void VPass::end()
{
    vkCmdEndRenderPass(m_cmd);
}

void allocate(VRenderObject obj)
{
    /* allocate data */
    VkDeviceSize vertsize = robj.size() * sizeof(VVertex);
    vertexbuffer->allocate(vertsize);
    stagebuffer->allocate(vertsize);
    stagebuffer->copy(vertexbuffer);
    stagebuffer->deallocate();

    if (robj.indices())
    {
        VkDeviceSize indsSize = sizeof(inds[0]) * inds.size();
        indexbuffer->allocate(indsSize);
        stagebuffer->allocate(indsSize);
        stagebuffer->copy(indexbuffer);
        stagebuffer->deallocate();
    }
}
