/**
 * @copyright DEFAULT
 * @brief: Buffer object that is CPU accessible memory to upload 
 *         the data from the vertex array to, and the final
 *         vertex buffer in device local memory. We'll then
 *         use a buffer copy command to move the data from
 *         the staging buffer to the actual vertex buffer.
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
