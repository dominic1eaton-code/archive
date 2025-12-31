/**
 * @copyright DEFAULT
 * @brief: Top level renderer. Converts a logical Scene model 
 *         with SceneObjects to renderable RenderScene model 
 *         with RenderSceneObjects and draw on screen.
 * @note : N/A
 */

#include "Renderer.h"

using namespace VulkanEngine;

bool Renderer::draw()
{
	//check if window is minimized and skip drawing
    if (m_window->minimized())
        return;

    // get command buffer for writing rendering commands
    VkCommandBuffer cmd = m_command->buffer();
    
    // Perform render pass that populates command buffer
    // with rendering commands
    for (const auto& pass : m_passes) 
    {
        pass->render(cmd, _renderobjects);
    }

    // submit populated command buffer to queue to begin exeuction of commands on GPU
    VK_CHECK(vkQueueSubmit(m_queues->graphics(), 1, &submitInfo, VK_NULL_HANDLE))

    // present results from queue submission to screen.
    // This is the final command that actually draws objects
    // on the screen
    VK_CHECK(vkQueuePresentKHR(m_queues->present(), &presentInfo));

    // increase frames
    m_frames++;
}
