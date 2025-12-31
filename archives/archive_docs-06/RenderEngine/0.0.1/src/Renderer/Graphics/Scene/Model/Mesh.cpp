/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Mesh.h"
#include "Logger.h"

using namespace RenderEngine;

Mesh::Mesh()
    : m_position({0.0f, 0.0f, 0.0f})
    , m_color({1.0f, 1.0f, 1.0f})
    , m_scale(0.3f)
    , m_size(0.5f)
    , m_index(0)
{}

Mesh::Mesh(glm::vec3 position, glm::vec3 color, float scale, int index)
    : m_position(position)
    , m_color(color)
    , m_scale(scale)
    , m_size(0.5f)
    , m_index(index)
{}

Mesh::~Mesh()
{}

int Mesh::index()
{
    return m_index;
}

glm::vec3 Mesh::position()
{
    return m_position;
}

glm::vec3 Mesh::color()
{
    return m_color;
}

glm::vec3 Mesh::normal()
{
    return m_normal;
}

float Mesh::scale()
{
    return m_scale;
}

glm::vec3 Mesh::size()
{
    return m_size;
}

const std::vector<Vertex> Mesh::vertices()
{
    return m_vertices;
}

const std::vector<uint16_t> Mesh::indices()
{
    return m_indices;
}

void Mesh::updateVertices()
{}

bool Mesh::indexed()
{
    m_indexed = !indices().empty();
    return m_indexed;
}

void Mesh::rescale(float scale)
{
    m_scale = scale;
}

void Mesh::reposition(glm::vec3 position)
{
    m_position = position;
}

void Mesh::changeColor(glm::vec3 color)
{
    m_color = color;
}

void Mesh::resize(glm::vec3 size)
{
    m_size = size;
}
