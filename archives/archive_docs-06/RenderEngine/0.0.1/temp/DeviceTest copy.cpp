/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
// #include <SDL2/SDL.h>
#include <iostream>
#include <filesystem>
#include <vector>
#include "Logger.h"
#include "VulkanCommon.h"
#include "VInstance.h"
#include "VWindow.h"
#include "PhysicalDevice.h"
#include "LogicalDevice.h"
#include "Buffer/SwapChain.h"
#include "Pipeline/GraphicsPipeline.h"
#include "Pipeline/Shader.h"
#include "Pipeline/Command.h"
#include "Pipeline/ColorPass.h"

namespace fs = std::filesystem;

void initialize()
{

}

void update()
{

}

int main(int argc, char **argv) 
{
    /* initialize */
    LoggingTool::Logger* m_logger = new LoggingTool::Logger();
    m_logger->enable();
    std::string m_logunit = "DeviceTest";

    // default application info from ENGINE
    VkApplicationInfo appInfo{};
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "RenderEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "RenderEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    /*  device setup */
    RenderEngine::VInstance* m_instance = new RenderEngine::VInstance(appInfo);
    RenderEngine::VWindow* m_window = new RenderEngine::VWindow(m_instance->instance());
    RenderEngine::PhysicalDevice* m_physicalDevice = new RenderEngine::PhysicalDevice(m_instance->instance(), m_window->surface());
    RenderEngine::LogicalDevice* m_logicalDevice = new RenderEngine::LogicalDevice(m_physicalDevice->device(), 
                                                                                   m_physicalDevice->info().features,
                                                                                   m_physicalDevice->queueInfo(),
                                                                                   m_physicalDevice->info().extensions);

    /* presentation setup */
    RenderEngine::SwapChain* m_swapchain = new RenderEngine::SwapChain(m_logicalDevice->device(), m_physicalDevice->indices(), m_window->surface(),
                                                                       m_physicalDevice->info().formats, m_physicalDevice->info().presentModes,
                                                                       m_physicalDevice->info().capabilities, m_window->extentPixels());

    /* graphics setup */
    // load default shaders
    fs::path shaderLibPath{"D:/dev/projects/RenderEngine/assets/shaders"};
    fs::path defaultShaderVert = shaderLibPath / "compiled" / "default.vert.spv";
    fs::path defaultShaderFrag = shaderLibPath / "compiled" / "default.frag.spv";
    RenderEngine::Shader* defaultVert = new RenderEngine::Shader(m_logicalDevice->device(), defaultShaderVert.string(), VK_SHADER_STAGE_VERTEX_BIT);
    RenderEngine::Shader* defaultFrag = new RenderEngine::Shader(m_logicalDevice->device(), defaultShaderFrag.string(), VK_SHADER_STAGE_FRAGMENT_BIT);
    std::vector<RenderEngine::Shader*> defaultShaders;
    defaultShaders.push_back(defaultVert);
    defaultShaders.push_back(defaultFrag);

    // create default graphics pipeline
    RenderEngine::GraphicsPipeline* defaultPipeline = new RenderEngine::GraphicsPipeline(m_logicalDevice->device(), defaultShaders, m_swapchain->extent(),  m_swapchain->format());
    m_swapchain->createFrameBuffers(defaultPipeline->renderPass());

    /* scene setup */

    /* setup drawing */
    // vulkan command executor
    RenderEngine::Command* m_command = new RenderEngine::Command(m_logicalDevice->device(), m_physicalDevice->indices().graphicsFamily.value());

    // graphics render passess
    RenderEngine::ColorPass* m_colorpass = new RenderEngine::ColorPass(m_swapchain->extent(), m_swapchain->framebuffers(), defaultPipeline);
    std::vector<RenderEngine::ColorPass*> defaultPasses;
    defaultPasses.push_back(m_colorpass);


    // @temp sync objects
    VkSemaphore imageAvailableSemaphore;
    VkSemaphore renderFinishedSemaphore;
    VkFence inFlightFence;
    VkSemaphoreCreateInfo semaphoreInfo{};
    semaphoreInfo.sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO;
    VkFenceCreateInfo fenceInfo{};
    fenceInfo.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
    fenceInfo.flags = VK_FENCE_CREATE_SIGNALED_BIT;
    RenderEngine::Utilities::checkVKCreation(vkCreateSemaphore(m_logicalDevice->device(), &semaphoreInfo, nullptr, &imageAvailableSemaphore));
    RenderEngine::Utilities::checkVKCreation(vkCreateSemaphore(m_logicalDevice->device(), &semaphoreInfo, nullptr, &renderFinishedSemaphore));
    RenderEngine::Utilities::checkVKCreation(vkCreateFence(m_logicalDevice->device(), &fenceInfo, nullptr, &inFlightFence));

    /* Draw Frame */
    // To use the right objects every frame, we need to keep track of the current frame. We will use a frame index for that purpose:
    uint32_t currentFrame = 0;

	//main loop
	// SDL_Event e;
	// bool bQuit = false;
    // int _selectedShader = 0;
	// while (!bQuit)
	// {
    //     //Handle events on queue
	// 	while (SDL_PollEvent(&e) != 0)
	// 	{
	// 		//close the window when user alt-f4s or clicks the X button			
	// 		if (e.type == SDL_QUIT)
	// 		{
	// 			bQuit = true;
	// 		}
	// 		else if (e.type == SDL_KEYDOWN)
	// 		{
	// 			if (e.key.keysym.sym == SDLK_SPACE)
	// 			{
	// 				_selectedShader += 1;
	// 				if (_selectedShader > 1)
	// 				{
	// 					_selectedShader = 0;
	// 				}
	// 			}
	// 		}
	// 	}

        // At the start of the frame, we want to wait until the previous frame has finished, so that the command buffer and semaphores are available to use.
        vkWaitForFences(m_logicalDevice->device(), 1, &inFlightFence, VK_TRUE, UINT64_MAX);
        vkResetFences(m_logicalDevice->device(), 1, &inFlightFence);

        // acquire an image from the swap chain. Recall that the swap chain is an extension feature, so we must use a function with the vk*KHR naming convention:?
        uint32_t imageIndex;
        vkAcquireNextImageKHR(m_logicalDevice->device(), m_swapchain->buffer(), UINT64_MAX, imageAvailableSemaphore, VK_NULL_HANDLE, &imageIndex);

        // With the imageIndex specifying the swap chain image to use in hand, we can now record the command buffer. 
        m_command->reset();

        // populate draw commands and add to command execution buffer
        // @todo make into template
        m_command->record(defaultPasses, imageIndex);

        // submit the command buffer
        m_command->submit(imageAvailableSemaphore, renderFinishedSemaphore, inFlightFence, m_logicalDevice->graphicsQueue());

        /* m_command-present() */
        // The last step of drawing a frame is submitting the result back to the swap chain to have it eventually show up on the screen
        VkPresentInfoKHR presentInfo{};
        presentInfo.sType = VK_STRUCTURE_TYPE_PRESENT_INFO_KHR;

        // The first two parameters specify which semaphores to wait on before presentation can happen, just like VkSubmitInfo. Since we want
        // to wait on the command buffer to finish execution, we take the semaphores which will be signalled and wait on them, thus we use signalSemaphores.
        VkSemaphore signalSemaphores[] = {renderFinishedSemaphore};
        presentInfo.waitSemaphoreCount = 1;
        presentInfo.pWaitSemaphores = signalSemaphores;

        // he next two parameters specify the swap chains to present images to and the index of the image for each swap chain. This will almost always be a single one.
        VkSwapchainKHR swapChains[] = {m_swapchain->buffer()};
        presentInfo.swapchainCount = 1;
        presentInfo.pSwapchains = swapChains;
        presentInfo.pImageIndices = &imageIndex;

        // It allows you to specify an array of VkResult values to check for every individual swap chain if presentation was
        // successful. It's not necessary if you're only using a single swap chain, because you can simply use the return value
        // of the present function.
        presentInfo.pResults = nullptr; // Optional

        // submits the request to present an image to the swap chain
        vkQueuePresentKHR(m_logicalDevice->presentQueue(), &presentInfo);
    // }

    // // cleanup
    // vkDestroySemaphore(m_logicalDevice->device(), imageAvailableSemaphore, nullptr);
    // vkDestroySemaphore(m_logicalDevice->device(), renderFinishedSemaphore, nullptr);
    // vkDestroyFence(m_logicalDevice->device(), inFlightFence, nullptr);
    return 0;
}
