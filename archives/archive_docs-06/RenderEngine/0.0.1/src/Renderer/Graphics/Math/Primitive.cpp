/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Primitive.h"
#include "Logger.h"

using namespace RenderEngine;

Primitive::Primitive()
    : m_position({0.0f, 0.0f})
    , m_scale(0.5f)
    , m_color({0.5f, 0.5f, 0.5f})
    , m_size(0.5f)
{}

Primitive::Primitive(glm::vec2 position, float scale, glm::vec3 color)
    : m_position(position)
    , m_scale(scale)
    , m_color(color)
    , m_size(0.5f)
{}

Primitive::~Primitive()
{}

const std::vector<Vertex> Primitive::vertices()
{
    return m_vertices;
}

const std::vector<uint16_t> Primitive::indices()
{
    return m_indices;
}

void Primitive::updateVertices()
{}

void Primitive::resize(float size)
{
    m_size = size;
}

void Primitive::rescale(float scale)
{
    m_scale = scale;
}

void Primitive::reposition(glm::vec2 position)
{
    m_position = position;
}

void Primitive::changeColor(glm::vec3 color)
{
    m_color = color;
}
