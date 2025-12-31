/**
 * @copyright DEFAULT
 * @brief: Main Engine class
 * @note : N/A
 */
#pragma once

#ifndef RENDERER_H
#define RENDERER_H

namespace RenderEngine
{
    class VWindow;
    class VInstance;

    class Renderer
    {
    public:
        Renderer(); 
        virtual ~Renderer(void);

        /* component transistion functions */
        void configure(void);
        void initialize(void);
        void pause(void);
        void shutdown(void);
        void update(void);
        void reset(void);
        void oneFrame(void);

        /* Perform render draw command */
        bool draw();
    
    private:
    };
} // RenderEngine

#endif // RENDERER_H
