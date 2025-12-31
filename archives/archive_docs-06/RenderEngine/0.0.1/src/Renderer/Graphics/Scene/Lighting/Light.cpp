/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Light.h"
#include "Logger.h"

using namespace RenderEngine;

Light::Light()
    : m_ambient({0.5, 0.5, 0.5})
    , m_diffuse({0.5, 0.5, 0.5})
    , m_specular({0.5, 0.5, 0.5})
    , m_shine(0.5)
{
    m_gpu = {m_ambient, m_diffuse, m_specular, m_shine};
}

Light::~Light()
{}
