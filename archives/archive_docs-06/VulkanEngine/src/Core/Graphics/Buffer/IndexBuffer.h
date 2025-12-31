/**
 * @copyright DEFAULT
 * @brief: index buffer is essentially an array of pointers
 *         into the vertex buffer. It allows you to reorder
 *         the vertex data, and reuse existing data for
 *         multiple vertices.
 * @note : buffers do not automatically allocate memory
 *         for themselves
 */
#pragma once

#include <string>

#ifndef STAGEBUFFER_H
#define STAGEBUFFER_H

namespace VulkanEngine
{

    class VKENGINE_API StageBuffer : public Buffer
    {
    public:
        StageBuffer();
        virtual ~StageBuffer(void);

        /* Create vulkan object */
        bool create(VWindow* window, Device device);

    private:
      
      
    };
} // VulkanEngine

#endif // STAGEBUFFER_H
