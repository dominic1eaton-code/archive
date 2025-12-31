/**
 * @copyright DEFAULT
 * @brief: VWindow wrapper class
 * @note : N/A
 */
#pragma once

#include <string>
#include <vector>
#include <optional>
#include "VulkanDefines.h"

#ifndef VWINDOW_H
#define VWINDOW_H

// define Window class constants
const uint32_t DEFAULT_WINDOW_WIDTH = 800;
const uint32_t DEFAULT_WINDOW_HEIGHT = 600;

// forward declerations
namespace LoggingTool { class Logger; }
struct SDL_Window;

namespace RenderEngine
{
    /* Types of windows supported by application */
    typedef enum
    {
        GLFW = 0,
        SDL = 1
    } WindowAPIType; 

    class RENGINE_API VWindow
    {
    public:
        VWindow();
        VWindow(VkInstance instance);
        virtual ~VWindow(void);

        /* create the window */
        bool create(VkInstance instance);

        // SDL
        /* Get window handle reference */
        struct SDL_Window* hwnd();

        /*  Window surface */
        VkSurfaceKHR surface();

        /* */
        VkExtent2D extent();

        /* */
        VkExtent2D extentPixels();

    private:
        // SDL
        /* SDL window*/
        struct SDL_Window* m_window;

        /* window created */
        bool m_created;

        /* Window name */
        std::string m_name;

        /* Window extent */
        VkExtent2D m_extent;
    
        /* Window extent in pixels */
        VkExtent2D m_extentPixels;

        /*  Window surface */
        VkSurfaceKHR m_surface;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // VWINDOW_H