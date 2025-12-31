/**
 * @copyright DEFAULT
 * @brief: TEMP Main Engine execution
 * @note : N/A
 */

#include <iostream>
#include "Devices/VInstance.h"
#include "Devices/PhysicalDevice.h"
#include "Devices/VWindow.h"
#include "Devices/LogicalDevice.h"
#include "Logger.h"
#include <SDL2/SDL_vulkan.h>

using namespace RenderEngine;

void initialize()
{
    // configuration
    LoggingTool::Logger* logger = new LoggingTool::Logger();
    logger->enable();
    logger->log("main", LoggingTool::LoggingLevel::INFO) << "Running Graphics" << LoggingTool::Logger::endl;
   
    VkApplicationInfo appInfo{};
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "RenderEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "RenderEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    /*  SETUP */
    // device
    VInstance* m_instance = new VInstance(appInfo);
    PhysicalDevice* physicalDevice = new PhysicalDevice();
    VWindow* m_window = new VWindow();
	VkSurfaceKHR _surface;
    LogicalDevice* logicalDevice = new LogicalDevice(m_instance); 
    VSurface* m_surface = new VSurface(m_instance);
    Swapchain* m_swapchain = new Swapchain(m_instance);
    GraphicsPipeline* m_graphicsPipeline = new GraphicsPipeline(m_instance);

    m_window->create();
    physicalDevice->select(m_instance->instance(), m_surface->surface());
    logicalDevice->create(physicalDevice->primary(), physicalDevice->features(), physicalDevice->queuesInfo());
    m_surface->create(m_window->hwnd(), m_instance->instance(), physicalDevice->primary())
    m_swapchain->create();

    // render pipelines
    m_graphicsPipeline->create(); // default render pipeline
    m_raytracePipeline->create();

    // render passes
    ColorPass colorPass();
    LightPass lightPass();
    ShadowPass shadowPass();

    m_passes->register(colorPass);
    m_passes->register(lightPass);
    m_passes->register(shadowPass);

    m_passes->enable(colorPass);
    m_passes->enable(lightPass);
    m_passes->enable(shadowPass);

    // assets -> AssetManager, AssetManagerCache
    //// shaders
    //// textures / materials / images
    //// meshes / models
    //// fonts / texts
    //// other assets ...

    /* DRAW */
    // call update()
    
    logger->log("main", LoggingTool::LoggingLevel::INFO) << "Running Graphics complete" << LoggingTool::Logger::endl;
}

void update()
{
    // draw
    //check if window is minimized and skip drawing
    if (SDL_GetWindowFlags(_window) & SDL_WINDOW_MINIMIZED)
        return;

    //wait until the gpu has finished rendering the last frame. Timeout of 1 second
    VK_CHECK(vkWaitForFences(_device, 1, &get_current_frame()._renderFence,  true, 1000000000));
    VK_CHECK(vkResetFences(_device, 1, &get_current_frame()._renderFence));

    //now that we are sure that the commands finished executing, we can safely reset the command buffer to begin recording again.
    VK_CHECK(vkResetCommandBuffer(get_current_frame()._mainCommandBuffer, 0));

    //request image from the swapchain
    uint32_t swapchainImageIndex;
    VK_CHECK(vkAcquireNextImageKHR(_device, _swapchain, 1000000000, get_current_frame()._presentSemaphore, nullptr, &swapchainImageIndex));

    //naming it cmd for shorter writing
    VkCommandBuffer cmd = get_current_frame()._mainCommandBuffer;

    //begin the command buffer recording. We will use this command buffer exactly once, so we want to let vulkan know that
    VkCommandBufferBeginInfo cmdBeginInfo = vkinit::command_buffer_begin_info(VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT);
    
    // perform subpass commands
    VK_CHECK(vkBeginCommandBuffer(cmd, &cmdBeginInfo));
    for (auto pass : passes)
    {
        pass->initialize(cmd);
        pass->begin();
        pass->draw(renderObjects);
        pass->end();
    }
    VK_CHECK(vkEndCommandBuffer(cmd)); // finalize the command buffer (we can no longer add commands, but it can now be executed)

    // Presentation
    VkPresentInfoKHR presentInfo{};
    presentInfo.sType = VK_STRUCTURE_TYPE_PRESENT_INFO_KHR;
    presentInfo.waitSemaphoreCount = 1;
    presentInfo.pWaitSemaphores = signalSemaphores;

    VkSwapchainKHR swapChains[] = { swapChain };
    presentInfo.swapchainCount = 1;
    presentInfo.pSwapchains = swapChains;
    presentInfo.pImageIndices = &imageIndex;
    presentInfo.pResults = nullptr; // Optional

    // !!!!!!!!!!!!!! DRAW !!!!!!!!!!!!!!
    std::cout << "!!!!!!!!!!!!!! DRAW !!!!!!!!!!!!!!" << std::endl;
    vkQueuePresentKHR(presentQueue, &presentInfo);

    // Handle frame resizes
    //      It is important to do this after vkQueuePresentKHR to
    //      ensure that the semaphores are in a consistent state,
    //      otherwise a signalled semaphore may never be properly
    //      waited upon.
    std::vector<VkFence> inFlightFences;
    size_t currentFrame = 0;
}

void init_scene()
{
    // init scene
    // create test objects
    // SceneObject monkey("Aslan");
    // Model monkey("Aslan");
    // monkey.mesh(meshLibrary.load("monkey"));
    // monkey.material(new Material(materialLibrary.load("wood_0")));
    // monkey.transform(Transform(0, 0, 0));

    // // SceneObject square();
    // Model square();
    // square.mesh(new Mesh(Primitive(Primitives::square)));
    // square.material(new Material("green"));
    // square.transform(Transform(0, 0, 0));

    // SceneObject triangle("test");
    Model triangle("test");
    triangle.mesh(new Mesh(Primitive(Primitives::triangle)));
    triangle.material(new Material("red"));
    triangle.transform(Transform(0, 0, 0));

    Camera* camera = new Camera();
    camera.transform(Transform(0, 0, 0));

    Environment* environment = new Environment();

    m_scene->register(monkey);
    m_scene->register(triangle);
    m_scene->register(square);
    m_scene->register(camera);
    m_scene->register(environment);
}

void drawScene()
{
    // bind buffer data from logical scene objects to GPU objects
    // camera data
    GPUCamera gpucamera;
    gpucamera.projection = camera.projection;
    gpucamera.view = camera.view;
    gpucamera.viewproj = camera.view * camera.projection;
    cameraBuffer->allocate(gpucamera);

    // environment data
    GPUEnvironment gpuenvironment;
    gpuenvironment.projection = environment.environment;
    environmentBuffer->allocate(gpuenvironment);

    // model data
    GPUModelSSBO* modelSSBO = new GPUModelSSBO();
    
    modelBuffer->allocate();

    // populate draw commands

}

int call()
{
    // initialize vulkan
    init_vulkan();
    init_editor();
    init_renderer();
    init_scene();

    while (m_renderer->isRunning())
    {
        SDL_Event event;
        while (SDL_PollEvent(&event))
        {
            // poll until all events are handled!
            // decide what to do with this event.
            if (event.type == SDL_QUIT)
            {
                SDL_Log("Program quit after %i ticks", e.quit.timestamp);
                m_renderer->shutdown();
            }
           
        }

        m_renderer->draw(m_scene);
        // update game state, draw the current frame
    }

}

int main(int argc, char **argv)
{
    call();
    return 0;
}
