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
    class Systen;

    class Engine
    {
    public:
        Engine();
        virtual ~Engine(void);

        /* create the Engine */
        bool create();

    private:
        // TEMP: Implement systems
        /* Engine Components */
        /*  Primary Renderer */
        // Renderer* m_Renderer;

        /* Engine Systems */
        Systen* m_renderSystem;
        Systen* m_audioSystem;
    };
} // VulkanEngine

#endif // ENGINE_H

