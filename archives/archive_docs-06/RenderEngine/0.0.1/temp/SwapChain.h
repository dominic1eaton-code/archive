/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef SWAPCHAIN_H
#define SWAPCHAIN_H

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API SwapChain
    {
    public:
        SwapChain();
        // SwapChain();
        virtual ~SwapChain(void);
    };
}

#endif // SWAPCHAIN_H