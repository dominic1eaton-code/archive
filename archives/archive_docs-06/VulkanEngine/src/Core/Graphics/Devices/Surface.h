/**
 * @copyright DEFAULT
 * @brief: Vulkan Surface wrapper class. Establishes the
 *         connection between Vulkan and the window system
 *         to present results to the screen
 * @note : N/A
 */
#pragma once

#ifndef SURFACE_H
#define SURFACE_H

namespace VulkanEngine
{
    class VulkanLogger;
    class Surface;

    class VKENGINE_API Surface
    {
    public:
        Surface();

        virtual ~Surface(void);

        VkSurfaceKHR create();

        void initialize(VkInstance instance, GLFWwindow* window);

    private:
        VkSurfaceKHR m_surface;

        VkWin32SurfaceCreateInfoKHR m_createInfo;

        VkStructureType m_sType;

        // HWND hwnd;

        // HINSTANCE m_hinstance;
        
        const void* m_pNext;

        VkWin32SurfaceCreateFlagsKHR m_flags;

        VulkanLogger* m_logger;

        GLFWwindow* m_window;

        VkInstance m_instance;
    };
}
#endif