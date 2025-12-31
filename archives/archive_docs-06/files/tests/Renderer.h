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

    private:
        uint32_t m_id;                    //
        bool m_keepSync;                  //
        uint32_t m_maxThreads;            //
        std::string m_role;               //
        std::string m_name;               //
        uint32_t m_rateDivisor;           //
        uint32_t m_callOffset;            //
        uint32_t m_execRate;              //
        std::string m_name;               // Unique instance name
        std::string m_configFile;         // Instance configuration file name
        SCommunicationLayer* m_commLayer; // Communication Service object
        SIntervalTimer* m_timer;          // Component time
        double m_iterRate;                // Iteration rate [hz]
        double m_timeStep;                // Time step [s]
        double m_timeStepActual;          // Time step with overframe [s]
        int m_offset;                     // Component frame offset
        
        enum TimeEnum
        {
            IDEAL,
            ACTUAL
        };
    };
} // VulkanEngine

#endif // RENDERER_H

