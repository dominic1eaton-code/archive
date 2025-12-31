/**
 * @copyright DEFAULT
 * @brief: Swapchain wrapper class
 * @note : N/A
 */

#include "Swapchain.h"
#include "Logger.h"

using namespace RenderEngine;

Swapchain::Swapchain()
    : m_logunit("Swapchain")
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

Swapchain::~Swapchain() {}

bool Swapchain::create()
{
    return true;
}