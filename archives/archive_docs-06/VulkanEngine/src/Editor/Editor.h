/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#pragma once

#ifndef ENGINE_H
#define ENGINE_H

namespace VulkanEngine
{
    class Renderer;

    class Engine
    {
    public:
        Engine();
        virtual ~Engine(void);

        /* create the Engine */
        bool create();

    private:
        /* Engine Components */
        /*  Primary Renderer */
        Renderer* m_Renderer;

        /* Engine Systems */

    };
} // VulkanEngine

#endif // ENGINE_H

