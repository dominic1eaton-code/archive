/**
 * @copyright DEFAULT
 * @brief: Swapchain will own frame buffers that will be
 *         presented to screen. Queue of images that are
 *         waiting to be presented to the screen
 * @note : N/A
 */
#pragma once

#include <string>

#ifndef VISTANCE_H
#define VISTANCE_H

namespace VulkanEngine
{
    class Device;

    class VKENGINE_API SwapChain
    {
    public:
        SwapChain();
        virtual ~SwapChain(void);

        /* Create vulkan object */
        bool create(VWindow* window, Device device);

    private:
      
      
    };
} // VulkanEngine

#endif // VISTANCE_H
