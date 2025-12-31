/**
 * @copyright DEFAULT
 * @brief: Swapchain wrapper class
 * @note : N/A
 */
#pragma once

#include <vulkan/vulkan.h>
#include <string>

#ifndef Swapchain_H
#define Swapchain_H

namespace LoggingTool
{
    class Logger;
}

namespace RenderEngine
{
    /*
     * Swapchain wrapper class
     */
    // class VKENGINE_API Swapchain
    class Swapchain
    {
    public:
        Swapchain(VInstance* instance);
        virtual ~Swapchain(void);

        /* create vulkan object */
        bool create();

    private:
        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // Swapchain_H