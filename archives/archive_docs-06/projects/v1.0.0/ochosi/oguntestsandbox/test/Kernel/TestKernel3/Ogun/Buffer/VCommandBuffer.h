/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VCommandBuffer_h
#define VCommandBuffer_h

#include "VObject.h"
#include <vector>

namespace ogun
{


class VCommandBuffer
{
public:
    void begin();

    void end();

    void barrier(VkPipelineStageFlags srcStage, VkPipelineStageFlags dstStage, VkImageMemoryBarrier barrier);

private:

    VkCommandBuffer m_buffer;

    VkDevice m_device;

    VkCommandPool m_pool;

    VkQueue m_queue;
};

} // namespace ogun

#endif // VCommandBuffer_h