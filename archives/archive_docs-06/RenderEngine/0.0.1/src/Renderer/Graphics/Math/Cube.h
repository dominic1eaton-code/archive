/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef CUBE_H
#define CUBE_H

#include "Scene/Mesh.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API Cube : virtual public Mesh
    {
    public:
        Cube();
        Cube(glm::vec3 position, glm::vec3 color, float scale, int index);
        virtual ~Cube(void);
    
    protected:
        /* */
        void updateVertices() override;

        /* */
        void updateIndices() override;
    };
}

#endif // CUBE_H