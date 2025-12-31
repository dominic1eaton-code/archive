/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef TRIANGLE_H
#define TRIANGLE_H

#include "Scene/Mesh.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API Triangle : virtual public Mesh
    {
    public:
        Triangle();
        Triangle(glm::vec3 position, float scale, glm::vec3 color);
        virtual ~Triangle(void);
    
    protected:
        /* */
        void updateVertices() override;

        /* */
        void updateIndices() override;
    };
}

#endif // TRIANGLE_H