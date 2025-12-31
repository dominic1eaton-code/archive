/**
 * @copyright DEFAULT
 * @brief: Top level renderer. Converts a logical Scene model 
 *         with SceneObjects to renderable RenderScene model 
 *         with RenderSceneObjects and draw on screen.
 * @note : N/A
 */
#pragma once

#include <string>

#ifndef RENDERER_H
#define RENDERER_H

namespace VulkanEngine
{
    class SceneManager;
    class SCommunicationLayer;
    class SIntervalTimer;

    class Renderer // : public Component
    {
    public:
        Renderer();
        virtual ~Renderer(void);

        /* draw scene objects */
        bool draw();

    private:
        /* Manage logical and renderable scenes processed by Renderer */
        SceneManager* m_sceneManager;

    // TEMP: implement component functions
    public:
        void initialize();
        void configure();
        void pause();
        void run();
        void reset();
        void shutdown();
        void nextmode();
        void changemode();
        void entermode();
        void exitmode();
    };
} // VulkanEngine

#endif // RENDERER_H

