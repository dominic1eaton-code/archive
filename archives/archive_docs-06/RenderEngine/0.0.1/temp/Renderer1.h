/**
 * @copyright DEFAULT
 * @brief: Renderer main class. Converts a logical scene (e.g. from an editor) to a render scene,
 *         via a series of rendering passes and draws result to screen.
 * @note : N/A
 */
#pragma once
#ifndef RENDERER_H
#define RENDERER_H

// #include <vulkan/vulkan.h>
#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>

// forward declerations
class Pipeline;
class Pass;
class Window;
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class VInstance;
    class VWindow;
    class PhysicalDevice;
    class LogicalDevice;
    class SwapChain;
    class GraphicsPipeline;
    class Command;
    class ColorPass;
    class Mesh;
    class Descriptor;

    class RENGINE_API Renderer
    {
    public:
        Renderer();
        virtual ~Renderer(void);

        /* initialize renderer*/
        bool initialize();

        /* configure renderer*/
        bool configure();

        /* update Renderer */
        bool update();

    private:
        /* Each frame should have its own command buffer, set of semaphores, and fence. Rename and then change them to be std::vectors of the objects:  */
        void drawFrame();

        // /* */
        // void  processEditorUpdates(bool bQuit, SDL_Event e);

        /* */
        void processEngineUpdates();

        /* Class Logger */
        LoggingTool::Logger* m_logger;

        /* Class Logging unit */
        std::string m_logunit;

        /* Render application vulkan information */
        VkApplicationInfo m_appInfo;

        /* */
        VInstance* m_instance;

        /* Handle to renderer drawing window */
        VWindow* m_window;
        
        /* */
        PhysicalDevice* m_physicalDevice;

        /* */
        LogicalDevice* m_logicalDevice;

        /* */
        SwapChain* m_swapchain;
    
        /* Vector of rendering pipelines */
        // std::vector<Pipeline> m_pipelines;
        GraphicsPipeline* m_defaultPipeline;

        /* */
        Command* m_command;

        // /* Vector of rendering passes */
        std::vector<ColorPass*> m_passes;

        /* */
        std::vector<VkSemaphore>  m_imageAvailableSemaphores;

        /* */
        std::vector<VkSemaphore>  m_renderFinishedSemaphores;

        /* */
        std::vector<VkFence> m_inFlightFences;

        /* To use the right objects every frame, we need to keep track of the current frame. We will
           use a frame index for that purpose: */
        uint32_t m_currentFrame;

        /* */
        std::vector<Mesh*> m_meshes;

        /* */
        Descriptor* m_descriptor;

        // /* Process renderer configuration files */
        // void processConfiguration();
    };
} // RenderEngine

#endif // RENDERER_H