/**
 * @copyright DEFAULT
 * @brief: Renderer wrapper class
 * @note : N/A
 */
#include "Renderer.h"
#include <iostream>
#include <filesystem>
#include <vector>
#include "Logger.h"
#include "VulkanCommon.h"
#include "VulkanConstants.h"
#include "VInstance.h"
#include "VWindow.h"
#include "PhysicalDevice.h"
#include "LogicalDevice.h"
#include "Buffer/SwapChain.h"
#include "Buffer/Descriptor.h"
#include "Pipeline/GraphicsPipeline.h"
#include "Pipeline/Shader.h"
#include "Pipeline/Command.h"
#include "Pipeline/ColorPass.h"
#include <SDL2/SDL.h>
#include "Math/Triangle.h"
#include "Math/Square.h"
#include "Math/Cube.h"
#include "Scene/Cameras/Camera.h"
#include "Scene/Lighting/Light.h"

using namespace RenderEngine;
namespace fs = std::filesystem;

Renderer::Renderer()
    : m_logunit("Renderer")
    , m_appInfo({})
    , m_currentFrame(0)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

Renderer::~Renderer() 
{
    for (size_t i = 0; i < Constants::MAX_FRAMES_IN_FLIGHT; i++)
    {
        vkDestroySemaphore(m_logicalDevice->device(), m_imageAvailableSemaphores[i], nullptr);
        vkDestroySemaphore(m_logicalDevice->device(), m_renderFinishedSemaphores[i], nullptr);
        vkDestroyFence(m_logicalDevice->device(), m_inFlightFences[i], nullptr);
    }
}

bool Renderer::initialize()
{
    /* initialize vulkan engine */
    // default application info from ENGINE
    m_appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    m_appInfo.pApplicationName = "RenderEngine";
    m_appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    m_appInfo.pEngineName = "RenderEngine";
    m_appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    m_appInfo.apiVersion = VK_API_VERSION_1_0;

    /*  device setup */
    m_instance = new VInstance(m_appInfo);
    m_window = new VWindow(m_instance->instance());
    m_physicalDevice = new PhysicalDevice(m_instance->instance(), m_window->surface());
    m_logicalDevice = new LogicalDevice(m_physicalDevice->device(), 
                                        m_physicalDevice->info().features,
                                        m_physicalDevice->queueInfo(),
                                        m_physicalDevice->info().extensions);

    /* presentation setup */
    m_swapchain = new SwapChain(m_logicalDevice->device(), m_physicalDevice->indices(), m_window->surface(),
                                m_physicalDevice->info().formats, m_physicalDevice->info().presentModes,
                                m_physicalDevice->info().capabilities, m_window->extentPixels(),
                                m_physicalDevice->info().depthFormat, m_physicalDevice->info().memoryProperties);

    /* graphics setup */
    // load default shaders
    fs::path shaderLibPath{"D:/dev/projects/RenderEngine/assets/shaders"};
    fs::path  = shaderLibPath / "compiled" / "lighting2.vert.spv";
    fs::path defaultShaderFdefaultShaderVertrag = shaderLibPath / "compiled" / "lighting2.frag.spv";
    Shader* defaultVert = new Shader(m_logicalDevice->device(), defaultShaderVert.string(), VK_SHADER_STAGE_VERTEX_BIT);
    Shader* defaultFrag = new Shader(m_logicalDevice->device(), defaultShaderFrag.string(), VK_SHADER_STAGE_FRAGMENT_BIT);
    std::vector<Shader*> defaultShaders;
    defaultShaders.push_back(defaultVert);
    defaultShaders.push_back(defaultFrag);

    // create default graphics pipeline
    m_descriptor = new Descriptor(m_logicalDevice->device());
    GraphicsPipeline* m_defaultPipeline = new GraphicsPipeline(m_logicalDevice->device(), defaultShaders, m_swapchain->extent(), m_swapchain->format(), m_descriptor->layout(), m_physicalDevice->info().depthFormat);
    m_swapchain->createFrameBuffers(m_defaultPipeline->renderPass());

    /* scene setup */
    /* setup drawing */
    // vulkan command executor
    m_command = new Command(m_logicalDevice->device(), m_physicalDevice->indices().graphicsFamily.value());

    // graphics render passess
    ColorPass* m_colorpass = new ColorPass(m_logicalDevice->device(), m_swapchain->extent(), m_swapchain->framebuffers(), m_defaultPipeline, m_physicalDevice->info().memoryProperties, m_descriptor->sets());
    m_descriptor->updateDescriptorSets(m_colorpass->uniformBuffers());
    m_passes.push_back(m_colorpass);

    // @temp sync objects
    m_imageAvailableSemaphores.resize(Constants::MAX_FRAMES_IN_FLIGHT);
    m_renderFinishedSemaphores.resize(Constants::MAX_FRAMES_IN_FLIGHT);
    m_inFlightFences.resize(Constants::MAX_FRAMES_IN_FLIGHT);

    VkSemaphoreCreateInfo semaphoreInfo{};
    semaphoreInfo.sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO;

    VkFenceCreateInfo fenceInfo{};
    fenceInfo.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
    fenceInfo.flags = VK_FENCE_CREATE_SIGNALED_BIT;

    for (size_t i = 0; i < Constants::MAX_FRAMES_IN_FLIGHT; i++)
    {
        Utilities::checkVKCreation(vkCreateSemaphore(m_logicalDevice->device(), &semaphoreInfo, nullptr, &m_imageAvailableSemaphores[i]));
        Utilities::checkVKCreation(vkCreateSemaphore(m_logicalDevice->device(), &semaphoreInfo, nullptr, &m_renderFinishedSemaphores[i]));
        Utilities::checkVKCreation(vkCreateFence(m_logicalDevice->device(), &fenceInfo, nullptr, &m_inFlightFences[i]));
    }
    return true;
}

bool Renderer::configure()
{
    // // read configuration files
    // ConfigFile rendererConfigFile();

    // // set default rendering pass
    // ColorPass* defaultPass = new defaultPass();
    // m_passes.append(defaultPass);
    return true;
}

// @tdod convert to systemlib
bool Renderer::update()
{
    /* ENGINE logical scene updates */
    setupEngineScene();

    // main draw loop
	bool bQuit = false;
	SDL_Event e;
    int _selectedShader = 0;
	while (!bQuit)
	{
        /* EDITOR i/o updates */
        // processEditorUpdates(bQuit, e);
        //Handle events on queue
        while (SDL_PollEvent(&e) != 0)
        {
            //close the window when user alt-f4s or clicks the X button			
            if (e.type == SDL_QUIT)
            {
                bQuit = true;
            }
            else if (e.type == SDL_KEYDOWN)
            {
                if (e.key.keysym.sym == SDLK_SPACE)
                {
                    _selectedShader += 1;
                    if (_selectedShader > 1)
                    {
                        _selectedShader = 0;
                    }
                }
            }
        }

        /* RENDERER draw updates */
        processEditoreUpdates();
        processEngineUpdates();
        drawFrame();
    }
    return true;
}

void Renderer::processEditoreUpdates()
{

}

void Renderer::drawFrame()
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
    m_command->record(m_passes, m_meshes, m_currentFrame, m_logicalDevice->transferQueue());

    // submit the command buffer to graphics queue to execute draw commands
    m_command->submit(m_imageAvailableSemaphores[m_currentFrame], m_renderFinishedSemaphores[m_currentFrame], m_inFlightFences[m_currentFrame], m_logicalDevice->graphicsQueue(), m_currentFrame);

    // submit the command buffer to present queue to draw on screen 
    m_command->present(m_renderFinishedSemaphores[m_currentFrame], imageIndex, m_logicalDevice->presentQueue(), m_swapchain->buffer());

    // update frames in flight
    m_currentFrame = (m_currentFrame + 1) % Constants::MAX_FRAMES_IN_FLIGHT;
}
