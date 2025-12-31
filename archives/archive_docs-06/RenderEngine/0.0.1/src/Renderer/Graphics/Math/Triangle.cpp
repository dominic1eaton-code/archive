/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Triangle.h"
#include "Logger.h"

using namespace RenderEngine;

Triangle::Triangle()
{
    updateVertices();
}

Triangle::Triangle(glm::vec3 position, float scale, glm::vec3 color)
    : Mesh(position, color, scale)
{
    updateVertices();
}

Triangle::~Triangle()
{}

void Triangle::updateVertices()
{
    m_vertices = {
        {{m_position[0]          , m_position[1] - m_scale, m_position[2]}, m_color},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2]}, m_color},
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2]}, m_color}
    };
}

void Triangle::updateIndices()
{}
