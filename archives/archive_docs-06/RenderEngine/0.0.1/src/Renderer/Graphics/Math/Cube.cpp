/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Cube.h"
#include "Logger.h"

using namespace RenderEngine;

Cube::Cube()
{
    updateVertices();
    updateIndices();
}

Cube::Cube(glm::vec3 position, glm::vec3 color, float scale, int index)
    : Mesh(position, color, scale, index)
{
    updateVertices();
    updateIndices();
}

Cube::~Cube()
{}

void Cube::updateVertices()
{
    m_vertices = {
        // bottom 0 1 2 3
        {{m_position[0] - m_scale, m_position[1] - m_scale, m_position[2]}, m_color, {0, 1, 0}, m_index},
        {{m_position[0] + m_scale, m_position[1] - m_scale, m_position[2]}, m_color, {0, 1, 0}, m_index},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2]}, m_color, {0, 1, 0}, m_index},
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2]}, m_color, {0, 1, 0}, m_index},

        // top 4 5 6 7
        {{m_position[0] - m_scale, m_position[1] - m_scale, m_position[2] - m_scale}, m_color, {0, 1, 0}, m_index}, // - glm::vec3(0.5f, 0.0f, 0.0f)},
        {{m_position[0] + m_scale, m_position[1] - m_scale, m_position[2] - m_scale}, m_color, {0, 1, 0}, m_index}, // - glm::vec3(0.5f, 0.0f, 0.0f)},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2] - m_scale}, m_color, {0, 1, 0}, m_index}, // - glm::vec3(0.5f, 0.0f, 0.0f)},
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2] - m_scale}, m_color, {0, 1, 0}, m_index}, // - glm::vec3(0.5f, 0.0f, 0.0f)},

        // front 0 1 5 4
        {{m_position[0] - m_scale, m_position[1] - m_scale, m_position[2]          }, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.5f, 0.0f)},
        {{m_position[0] + m_scale, m_position[1] - m_scale, m_position[2]          }, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.5f, 0.0f)},
        {{m_position[0] - m_scale, m_position[1] - m_scale, m_position[2] - m_scale}, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.5f, 0.0f)},
        {{m_position[0] + m_scale, m_position[1] - m_scale, m_position[2] - m_scale}, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.5f, 0.0f)},

        // back 2 3 7 6
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2]          }, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.0f, 1.0f)},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2]          }, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.0f, 1.0f)},
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2] - m_scale}, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.0f, 1.0f)},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2] - m_scale}, m_color, {0, 0, 1}, m_index}, // - glm::vec3(0.0f, 0.0f, 1.0f)},

        // left 0 4 7 3
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2]          }, m_color, {1, 0, 0}, m_index}, // - glm::vec3(1.0f, 1.0f, 1.0f)},
        {{m_position[0] - m_scale, m_position[1] - m_scale, m_position[2]          }, m_color, {1, 0, 0}, m_index}, // - glm::vec3(1.0f, 1.0f, 1.0f)},
        {{m_position[0] - m_scale, m_position[1] + m_scale, m_position[2] - m_scale}, m_color, {1, 0, 0}, m_index}, // - glm::vec3(1.0f, 1.0f, 1.0f)},
        {{m_position[0] - m_scale, m_position[1] - m_scale, m_position[2] - m_scale}, m_color, {1, 0, 0}, m_index}, // - glm::vec3(1.0f, 1.0f, 1.0f)},

        // right 5 1 2 6
        {{m_position[0] + m_scale, m_position[1] - m_scale, m_position[2]          }, m_color, {1, 0, 0}, m_index}, // - glm::vec3(0.5f, 0.5f, 0.5f)},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2]          }, m_color, {1, 0, 0}, m_index}, // - glm::vec3(0.5f, 0.5f, 0.5f)},
        {{m_position[0] + m_scale, m_position[1] - m_scale, m_position[2] - m_scale}, m_color, {1, 0, 0}, m_index}, // - glm::vec3(0.5f, 0.5f, 0.5f)},
        {{m_position[0] + m_scale, m_position[1] + m_scale, m_position[2] - m_scale}, m_color, {1, 0, 0}, m_index} // - glm::vec3(0.5f, 0.5f, 0.5f)}
    };
}

void Cube::updateIndices()
{
    m_indices = {
        0, 1, 2, 2, 3, 0, // top
        4, 5, 6, 6, 7, 4, // bottom
        0, 1, 5, 5, 4, 0, // front
        2, 3, 7, 7, 6, 2, // back
        0, 4, 7, 7, 3, 0, // left
        5, 1, 2, 2, 6, 5  // right
    };
}
