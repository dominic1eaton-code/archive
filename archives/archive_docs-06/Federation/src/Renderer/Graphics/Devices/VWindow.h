/**
 * @copyright DEFAULT
 * @brief: VWindow wrapper class
 * @note : N/A
 */
#pragma once

#include <SDL2/SDL.h>
#include <vulkan/vulkan.h>
#include <vector>
#include <string>
#include <optional>

#ifndef VWindow_H
#define VWindow_H


// define Window class constants
const uint32_t DEFAULT_WINDOW_WIDTH = 800;
const uint32_t DEFAULT_WINDOW_HEIGHT = 600;

namespace LoggingTool
{
    class Logger;
}

namespace RenderEngine
{

    /* Types of windows supported by application */
    typedef enum
    {
        GLFW = 0,
        SDL = 1
    } WindowType; 

    /*
     * VWindow wrapper class
     */
    // class VKENGINE_API VWindow
    class VWindow
    {
    public:
        VWindow();
        virtual ~VWindow(void);

        /* Get window handle reference */
        struct SDL_Window* hwnd();

        /* create the window */
        bool create();
        
    private:
        /* SDL window*/
        struct SDL_Window* m_window;

        /* Window name */
        std::string m_name;

        /* Window extent */
        VkExtent2D m_extent;
    
        /*  Window surface */
        VkSurfaceKHR m_surface;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // VWindow_H