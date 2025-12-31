/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef SQUARE_H
#define SQUARE_H

#include "Scene/Mesh.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API Square : virtual public Mesh
    {
    public:
        Square();
        Square(glm::vec3 position, float scale, glm::vec3 color);
        virtual ~Square(void);
    
    protected:
        /* */
        void updateVertices() override;

        /* */
        void updateIndices() override;
    };
}

#endif // SQUARE_H