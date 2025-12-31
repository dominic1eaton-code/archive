/**
 * @copyright DEFAULT
 * @brief: Buffer object to create regions of memory used
 *         for storing vertex data hat can be read by the
 *         graphics card.
 * @note : buffers do not automatically allocate memory 
 *         for themselves
 */
#pragma once

#include <string>

#ifndef VERTEXBUFFER_H
#define VERTEXBUFFER_H

namespace VulkanEngine
{

    class VKENGINE_API VertexBuffer : public Buffer
    {
    public:
        VertexBuffer();
        virtual ~VertexBuffer(void);

        /* Create vulkan object */
        bool create(VWindow* window, Device device);

    private:
      
      
    };
} // VulkanEngine

#endif // VERTEXBUFFER_H
