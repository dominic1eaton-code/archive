

#include "GPUCamera.h"


void GPUCamera::bind(GPUCameraData cameraData)
{
    void* data;
    vmaMapMemory(m_allocator, m_cameraBuffer.allocation(), &data);
    memcpy(data, &m_cameraData, sizeof(GPUCameraData));
    vmaUnmapMemory(m_allocator, m_cameraBuffer._allocation);
} 