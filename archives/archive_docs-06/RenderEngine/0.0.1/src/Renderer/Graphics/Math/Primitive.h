/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef PRIMITIVE_H
#define PRIMITIVE_H

#include "Vertex.h"
#include "Scene/SceneObject.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API Primitive : virtual public SceneObject
    {
    public:
        Primitive();
        Primitive(glm::vec2 position, float scale, glm::vec3 color);
        virtual ~Primitive(void);

        /* */
        virtual const std::vector<Vertex> vertices();

        /* */
        virtual const std::vector<uint16_t> indices();

    protected:
        /* */
        virtual void updateVertices() = 0;

        /* */
        virtual void updateIndices() = 0;

        /* */
        virtual void resize(float size);

        /* */
        virtual void rescale(float scale);

        /* */
        virtual void reposition(glm::vec2 position);

        /* */
        virtual void changeColor(glm::vec3 color);

        /* */
        std::vector<Vertex> m_vertices;

        /* */
        std::vector<uint16_t> m_indices;

        /* */
        glm::vec2 m_position;

        /* */
        glm::vec3 m_color;

        /* */
        float m_scale;

        /* */
        float m_size;
    };
}

#endif // PRIMITIVE_H