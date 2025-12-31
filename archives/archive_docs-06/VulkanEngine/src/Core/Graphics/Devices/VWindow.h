/**
 * @copyright DEFAULT
 * @brief: Generic Window wrapper class
 * @note : N/A
 */
#pragma once

#include <string>

#ifndef VWINDOW_H
#define VWINDOW_H

// define Window class constants
const uint32_t DEFAULT_WINDOW_WIDTH = 800;
const uint32_t DEFAULT_WINDOW_HEIGHT = 600;

namespace VulkanEngine
{
    class VulkanLogger;
    class Surface;

    typedef enum
    {
        GLFW = 0,
        SDL = 1
    } WindowType; 

    class VKENGINE_API VWindow
    {
    public:
        VWindow();
        virtual ~VWindow(void);

        /* Create window */
        bool create(VkInstance instance); 

        /* Window surface reference */
        VkSurfaceKHR surface();

        /* Window extent reference */
        VkExtent2D extent();

    private:
        /* Window object */
        SDL_Window* m_window;
        
        /* Window object */
        // GLFWwindow* m_window;

        /* Name of winodw to create */
        std::string m_windowName;

        /* Type of base window instance to create */
        WindowType m_windowType;

        /*  Window surface */
        Surface* m_surface;

        /*  Window internal surface */
        VkSurfaceKHR m_internalSurface;

        /* Window instance reference */
        VkInstance m_instance;

        /* Window extent */
        VkExtent2D m_extent;

        /* Window width */
        int m_width;

        /* Window height */
        int m_height;
    };
} // VulkanEngine

#endif // VWINDOW_H
