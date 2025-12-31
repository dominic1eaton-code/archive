/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef MESH_H
#define MESH_H

#include "Math/Vertex.h"
#include "Scene/SceneObject.h"
#include <glm/glm.hpp>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>
#include "Buffer/UniformBufferObject.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class Material;

    class RENGINE_API Mesh : virtual public SceneObject
    {
    public:
        Mesh();
        Mesh(glm::vec3 position, glm::vec3 color, float scale, int index);
        virtual ~Mesh(void);

        /* */
        virtual const std::vector<Vertex> vertices();

        /* */
        virtual const std::vector<uint16_t> indices();

        /* */
        virtual bool indexed();

        /* */
        glm::vec3 position();
        
        /* */
        glm::vec3 color();
        
        /* */
        glm::vec3 normal();
        
        /* */
        float scale();
        
        /* */
        glm::vec3 size();

        /* */
        int index();

        /* */
        Material* material();

        /* */
        void changeMaterial(Material* material)

    protected:
        /* */
        virtual void updateVertices() = 0;

        /* */
        virtual void updateIndices() = 0;

        /* */
        virtual void resize(glm::vec3 size);

        /* */
        virtual void rescale(float scale);

        /* */
        virtual void reposition(glm::vec3 position);

        /* */
        virtual void changeColor(glm::vec3 color);

        /* */
        bool m_indexed;

        /* */
        std::vector<Vertex> m_vertices;

        /* */
        std::vector<uint16_t> m_indices;

        /* */
        glm::vec3 m_position;

        /* */
        glm::vec3 m_color;

        /* */
        glm::vec3 m_normal;

        /* */
        float m_scale;

        /* */
        glm::vec3 m_size;

        /* */
        int m_index;

        /* */
        Material* m_material;
    };
}

#endif // MESH_H
