/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Scene.h"
#include "Logger.h"

using namespace RenderEngine;

Scene::Scene()
{}

Scene::Scene()
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

Scene::~Scene()
{
    vkDestroyDevice(m_swapChain, nullptr);
}
