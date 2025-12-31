/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VCommand.h"

using namespace ogun;


void VCommand::execute()
{
    vkResetM_cmd(m_m_cmds[currentFrame], 0);
    
    createVk(vkBeginM_cmd(m_m_cmds[currentFrame], &m_beginInfo));



    vkCmdBeginRenderPass(m_cmd, &m_renderPassInfo, m_subpassContents);

    record();

    vkCmdEndRenderPass(m_cmd);



    createVk(vkEndM_cmd(m_m_cmds[currentFrame]));

    createVk(vkQueueSubmit(graphicsQueue, 1, &submitInfo, inFlightFence));

    vkQueuePresentKHR(presentQueue, &presentInfo);
}

void VCommand::record(VRenderObject obj)
{
    /* populate commands */
    /* bind */
    vkCmdBindPipeline(m_cmd, bindpoint, pipeline);

    vkCmdBindVertexBuffers(m_cmd, vertexbuffer->first(), vertexbuffer->size(), vertexbuffer->data(), vertexbuffer->offsets());

    vkCmdBindIndexBuffer(m_cmd, indexbuffer->data(), indexbuffer->offset(), indexbuffer->type());

    vkCmdBindDescriptorSets(m_cmd, bindpoint, layout, descriptor->first(), descriptor->size(), descriptor->data(), 0, NULL);

    /* set dynamic states */
    if (m_dstate[DynamicState::VIEWPORT])
        vkCmdSetViewport(m_cmd, );

    if (m_dstate[DynamicState::SCISSOR])
        vkCmdSetScissor(m_cmd, );

    /* push */
    vkCmdPushConstants(m_cmd, layout, stageflags, offsets, size, pvalues);
 
    vkCmdBindDescriptorSets(m_cmd, );

    /* draw */
    vkCmdDraw(m_cmd, );

    vkCmdDrawIndirect(m_cmd, );

    vkCmdDrawIndirectCount(m_cmd, );

    vkCmdDrawIndexed(m_cmd, );

    vkCmdDrawIndexedIndirect(m_cmd, );

    vkCmdDrawIndexedIndirectCount(m_cmd, );

    /* compute */
    // vkCmdDispatch()
}
