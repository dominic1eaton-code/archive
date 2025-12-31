/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "SceneManager.h"
#include "Logger.h"

using namespace RenderEngine;

SceneManager::SceneManager()
{}

SceneManager::SceneManager()
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

SceneManager::~SceneManager()
{
    vkDestroyDevice(m_swapChain, nullptr);
}
