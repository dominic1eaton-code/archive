/**
 * @brief   
 * @note    N/A
 * @version 0.0.1
 * @copyright Copyright (c) 2023
 */
#include "VulkanEngine.h"

using namespace VulkanEngine;

void Engine::configure()
{
    
}

void Engine::initialize()
{
    // default application info from ENGINE
    m_instance = new VInstance(m_imports.appInfoMsg);
    m_window = new VWindow(); 
    m_physicalDevice = new PhysicalDevice();
    m_logicalDevice = new LogicalDevice();
    m_swapchain = new SwapChain();

    m_descriptors;
    m_pipelines;
    m_passes; // render passes

    m_command = new Command();

    m_imageAvailableSemaphores;
    m_renderFinishedSemaphores;
    m_inFlightFences;

}

void Engine::update()
{
    // process imports
    processImports();

    // process exports
    processExports();

    // main rendering draw frame
    drawFrame();
}

void Engine::processImports()
{
    while(createNewMeshEvent = m_imports.NextCreateNewMeshEvent() != NULL)
    {
        createMesh(createNewMeshEvent);
    }
    while(createNewCameraEvent = m_imports.NextCreateNewCameraEvent() != NULL)
    {
        createCamera(createNewCameraEvent);
    }
}

void Engine::drawFrame()
{
    // At the start of the frame, we want to wait until the previous frame has finished, so that the command buffer and semaphores are available to use.
    vkWaitForFences(m_logicalDevice->device(), 1, &m_inFlightFences[m_currentFrame], VK_TRUE, UINT64_MAX);
    vkResetFences(m_logicalDevice->device(), 1, &m_inFlightFences[m_currentFrame]);

    // acquire an image from the swap chain. Recall that the swap chain is an extension feature, so we must use a function with the vk*KHR naming convention:
    uint32_t imageIndex;
    vkAcquireNextImageKHR(m_logicalDevice->device(), m_swapchain->buffer(), UINT64_MAX, m_imageAvailableSemaphores[m_currentFrame], VK_NULL_HANDLE, &imageIndex);

    // With the imageIndex specifying the swap chain image to use in hand, we can now record the command buffer. Clearing command
    // buffer to prepare for use
    m_command->reset(m_currentFrame);

    // populate draw commands and add to command execution buffer
    // @todo make into template
    m_command->record(m_meshes, m_camera, m_currentFrame, m_logicalDevice->transferQueue());

    // submit the command buffer to graphics queue to execute draw commands
    m_command->submit(m_imageAvailableSemaphores[m_currentFrame], m_renderFinishedSemaphores[m_currentFrame], m_inFlightFences[m_currentFrame], m_logicalDevice->graphicsQueue(), m_currentFrame);

    // submit the command buffer to present queue to draw on screen 
    m_command->present(m_renderFinishedSemaphores[m_currentFrame], imageIndex, m_logicalDevice->presentQueue(), m_swapchain->buffer());

    // update frames in flight
    m_currentFrame = (m_currentFrame + 1) % Constants::MAX_FRAMES_IN_FLIGHT;
}
