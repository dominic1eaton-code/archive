/**
 * @copyright DEFAULT
 * @brief: GraphicsPipeline wrapper class
 * @note : N/A
 */
#pragma once

#include <vulkan/vulkan.h>
#include <string>

#ifndef GraphicsPipeline_H
#define GraphicsPipeline_H

namespace LoggingTool
{
    class Logger;
}

namespace RenderEngine
{
    /*
     * GraphicsPipeline wrapper class
     */
    // class VKENGINE_API GraphicsPipeline
    class GraphicsPipeline
    {
    public:
        GraphicsPipeline(VInstance* instance);
        virtual ~GraphicsPipeline(void);

        /* create vulkan object */
        bool create();

    private:
        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // GraphicsPipeline_H