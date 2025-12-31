/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Square.h"
#include "Logger.h"

using namespace RenderEngine;

Square::Square()
{
    updateVertices();
    updateIndices();
}

Square::Square(glm::vec3 position, float scale, glm::vec3 color)
    : Mesh(position, color, scale)
{
    updateVertices();
    updateIndices();
}

Square::~Square()
{}

void Square::updateVertices()
{
    m_vertices = {
        {{m_position[0] - m_scale, m_position[1] - m_scale, m_position[2]}, m_color},
        {{m_position[0] + m_scale, m_position[1] - m_scale, m_position[2]}, m_color},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2]}, m_color},
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2]}, m_color}
    };
}

void Square::updateIndices()
{
    m_indices = {
        0, 1, 2, 2, 3, 0
    };
}
