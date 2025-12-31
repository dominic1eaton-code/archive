/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Command.h"
#include "ColorPass.h"
#include "Logger.h"
#include "VulkanCommon.h"
#include "VulkanConstants.h"
#include "VulkanConstants.h"
#include "Scene/Mesh.h"

using namespace RenderEngine;

Command::Command()
{}

Command::Command(VkDevice device, uint32_t queueFamilyIndex)
    : m_device(device)
    , m_commandPool(VK_NULL_HANDLE)
    , m_commandPoolInfo({})
    , m_commandBufferAllocInfo({})
    , m_beginInfo({})
    , m_queueFamilyIndex(queueFamilyIndex)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    create();
}

Command::~Command()
{
    vkDestroyCommandPool(m_device, m_commandPool, nullptr);
}

void Command::create()
{
    // Commands in Vulkan, like drawing operations and memory transfers, are not
    // executed directly using function calls. You have to record all of the operations
    // you want to perform in command buffer objects
    // There are two possible flags for command pools
    //     VK_COMMAND_POOL_CREATE_TRANSIENT_BIT           : Hint that command buffers are re-recorded with new
    //                                                      commands very often (may change memory allocation behavior)
    //     VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT: Allow command buffers to be re-recorded individually,
    //                                                      without this flag they all have to be reset together
    m_commandPoolInfo.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;

    // We will be recording a command buffer every frame, so we want to be able to reset and re-record over it.
    // Thus, we need to set the VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT flag bit for our command pool.
    m_commandPoolInfo.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
    m_commandPoolInfo.queueFamilyIndex = m_queueFamilyIndex;

    // create vulkan object
    Utilities::checkVKCreation(vkCreateCommandPool(m_device,
                                                  &m_commandPoolInfo,
                                                   nullptr,
                                                  &m_commandPool));

    // The level parameter specifies if the allocated command buffers are primary or secondary command buffers.
    //     VK_COMMAND_BUFFER_LEVEL_PRIMARY  : Can be submitted to a queue for execution, but cannot be called
    //                                        from other command buffers.
    //     VK_COMMAND_BUFFER_LEVEL_SECONDARY: Cannot be submitted directly, but can be called from primary
    //                                        command buffers.
    m_commandBuffers.resize(Constants::MAX_FRAMES_IN_FLIGHT);
    m_commandBufferAllocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    m_commandBufferAllocInfo.commandPool = m_commandPool;
    m_commandBufferAllocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    m_commandBufferAllocInfo.commandBufferCount = (uint32_t) m_commandBuffers.size();

    // create vulkan object
    Utilities::checkVKCreation(vkAllocateCommandBuffers(m_device,
                                                       &m_commandBufferAllocInfo,
                                                        m_commandBuffers.data()));
}

// @todo make into template
void Command::record(std::vector<Mesh*> meshes, uint32_t currentFrame, VkQueue transferQueue)
{
    // start command buffer record
    begin(currentFrame);

    // record drawing commands for render pass
    for (auto pass : passes)
        pass->draw(m_commandBuffers[currentFrame], m_commandPool, currentFrame, meshes, transferQueue);

    // end command buffer record
    end(currentFrame);
}

void Command::begin(uint32_t currentFrame)
{
    m_beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;

    // The flags parameter specifies how we're going to use the command buffer. The following values are available:
    //     VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT     : The command buffer will be rerecorded right after executing
    //                                                       it once.
    //     VK_COMMAND_BUFFER_USAGE_RENDER_PASS_CONTINUE_BIT: This is a secondary command buffer that will be entirely within
    //                                                       a single render pass.
    //     VK_COMMAND_BUFFER_USAGE_SIMULTANEOUS_USE_BIT    : The command buffer can be resubmitted while it is also already
    //                                                       pending execution.
    m_beginInfo.flags = 0;                  // Optional

    // The pInheritanceInfo parameter is only relevant for secondary command buffers. It specifies which state to inherit
    // from the calling primary command buffers.
    m_beginInfo.pInheritanceInfo = nullptr; // Optional

    // If the command buffer was already recorded once, then a call to vkBeginCommandBuffer will implicitly reset it.
    // It's not possible to append commands to a buffer at a later time.
    Utilities::checkVKCreation(vkBeginCommandBuffer(m_commandBuffers[currentFrame],
                                                   &m_beginInfo));
}

void Command::end(uint32_t currentFrame)
{
    Utilities::checkVKCreation(vkEndCommandBuffer(m_commandBuffers[currentFrame]));
}

void Command::reset(uint32_t currentFrame)
{
    // make sure m_commandBuffers is able to be recorded
    vkResetCommandBuffer(m_commandBuffers[currentFrame], 0);
}

void Command::submit(VkSemaphore imageAvailableSemaphore,
                     VkSemaphore renderFinishedSemaphore,
                     VkFence inFlightFence,
                     VkQueue graphicsQueue,
                     uint32_t currentFrame)
{
     /** Submitting the command buffer **/
    VkSubmitInfo submitInfo{};
    submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;

    // The first three parameters specify which semaphores to wait on before execution begins and in which stage(s) of the pipeline to
    // wait. We want to wait with writing colors to the image until it's available, so we're specifying the stage of the graphics
    // pipeline that writes to the color attachment. That means that theoretically the implementation can already start executing
    // our vertex shader and such while the image is not yet available. Each entry in the waitStages array corresponds to the semaphore
    // with the same index in pWaitSemaphores.
    VkSemaphore waitSemaphores[] = {imageAvailableSemaphore};
    VkPipelineStageFlags waitStages[] = {VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT};
    submitInfo.waitSemaphoreCount = 1;
    submitInfo.pWaitSemaphores = waitSemaphores;
    submitInfo.pWaitDstStageMask = waitStages;

    // The next two parameters specify which command buffers to actually submit for execution. We simply submit the single command buffer we have.
    submitInfo.commandBufferCount = 1;
    submitInfo.pCommandBuffers = &m_commandBuffers[currentFrame];

    // The signalSemaphoreCount and pSignalSemaphores parameters specify which semaphores to signal once the command buffer(s) have finished
    // execution. In our case we're using the renderFinishedSemaphore for that purpose.
    VkSemaphore signalSemaphores[] = {renderFinishedSemaphore};
    submitInfo.signalSemaphoreCount = 1;
    submitInfo.pSignalSemaphores = signalSemaphores;

    // We can now submit the command buffer to the graphics queue using vkQueueSubmit. The function takes an array of VkSubmitInfo structures
    // as argument for efficiency when the workload is much larger. The last parameter references an optional fence that will be signaled when
    // the command buffers finish execution. This allows us to know when it is safe for the command buffer to be reused, thus we want to give
    // it inFlightFence. Now on the next frame, the CPU will wait for this command buffer to finish executing before it records new commands into it.
    RenderEngine::Utilities::checkVKCreation(vkQueueSubmit(graphicsQueue, 1, &submitInfo, inFlightFence));
}

void Command::present(VkSemaphore renderFinishedSemaphore, uint32_t imageIndex, VkQueue presentQueue, VkSwapchainKHR swapchain)
{
        /* m_command-present() */
        // The last step of drawing a frame is submitting the result back to the swap chain to have it eventually show up on the screen
        VkPresentInfoKHR presentInfo{};
        presentInfo.sType = VK_STRUCTURE_TYPE_PRESENT_INFO_KHR;

        // The first two parameters specify which semaphores to wait on before presentation can happen, just like VkSubmitInfo. Since we want
        // to wait on the command buffer to finish execution, we take the semaphores which will be signalled and wait on them, thus we use signalSemaphores.
        VkSemaphore signalSemaphores[] = {renderFinishedSemaphore};
        presentInfo.waitSemaphoreCount = 1;
        presentInfo.pWaitSemaphores = signalSemaphores;

        // the next two parameters specify the swap chains to present images to and the index of the image for each swap chain. This will almost always be a single one.
        VkSwapchainKHR swapChains[] = {swapchain};
        presentInfo.swapchainCount = 1;
        presentInfo.pSwapchains = swapChains;
        presentInfo.pImageIndices = &imageIndex;

        // It allows you to specify an array of VkResult values to check for every individual swap chain if presentation was
        // successful. It's not necessary if you're only using a single swap chain, because you can simply use the return value
        // of the present function.
        presentInfo.pResults = nullptr; // Optional

        // submits the request to present an image to the swap chain
        vkQueuePresentKHR(presentQueue, &presentInfo);
}
