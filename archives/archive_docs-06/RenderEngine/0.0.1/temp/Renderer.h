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

// forward declerations
class Pipeline;
class Pass;
class Window;
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    /*
     * Renderer main class
     */
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
        /* Class Logger */
        LoggingTool::Logger* m_logger;

        /* Class Logging unit */
        std::string m_logunit;

        // /* Render application vulkan information */
        // VkApplicationInfo m_appInfo;

        /* Handle to renderer drawing window */
        Window* m_window;
    
        // /* Vector of rendering pipelines */
        // std::vector<Pipeline> m_pipelines;

        // /* Vector of rendering passes */
        // std::vector<Pass> m_passes;

        // /* Process renderer configuration files */
        // void processConfiguration();
    };
} // RenderEngine

#endif // RENDERER_H