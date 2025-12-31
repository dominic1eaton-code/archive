/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "SwapChain.h"
#include "Logger.h"

using namespace RenderEngine;

SwapChain::SwapChain()
{}

SwapChain::SwapChain()
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

SwapChain::~SwapChain()
{
    vkDestroyDevice(m_swapChain, nullptr);
}
