/**
 * @copyright DEFAULT
 * @brief: VSurface wrapper class
 * @note : N/A
 */
#pragma once

#include <vulkan/vulkan.h>
#include <string>

#ifndef VSurface_H
#define VSurface_H

namespace LoggingTool
{
    class Logger;
}m_capabilities

namespace RenderEngine
{
    /*
     * VSurface wrapper class
     */
    // class VKENGINE_API VSurface
    class VSurface
    {
    public:
        VSurface(VInstance* instance);
        virtual ~VSurface(void);

        /* create vulkan object */
        bool create();

    private:
        /* surface */
        VkSurfaceKHR m_surface;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // VSurface_H