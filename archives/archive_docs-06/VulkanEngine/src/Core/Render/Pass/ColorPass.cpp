/**
 * @file
 * @brief  populates draw commands used by renderer
 * @author
 * @note
 */

#include "ColorPass.h"
#include "VInstance.h"
#include "Utility/VulkanUtil.h"

using namespace VulkanEngine;

ColorPass::ColorPass()
{}

ColorPass::~ColorPass()
{

}

// put draw commands on execution buffer
void ColorPass::draw(VkCommandBuffer cmd, std::vector<RenderObject> _renderobjects)
{
    /* write object data to be draw into memory */
    // begin mapping of data in memory
    m_memoryAllocator->map(data, buffer);

    // Copy logical scene objects data into renderable
    // GPU objects data in memory
    for(auto _gpuObject : gpuObjects)
    {
        _gpuObject->copy(_renderobjects[_gpuObject]);
    }

    // begin UNmapping of data in memory
    m_memoryAllocator->unmap(data, buffer);

    /* Bind drawing commands to command buffer */
    vkCmdBindPipeline(cmd);
    vkCmdBindDescriptorSets(cmd);
    vkCmdPushConstants(cmd);
    vkCmdBindVertexBuffers(cmd);
    vkCmdBindIndexBuffers(cmd);
    vkCmdDraw(cmd);
}

// memory allocator
template<typename T, typename U>
bool MemoryAllocator::allocate(T data, U buffer)
{
	void* ddata;
    // begin mapping of data in memory
    vmaMapMemory(m_allocator, buffer, &data);
    
    // move data into memory
    memcpy(ddata, &data, sizeof(T));

    // begin UNmapping of data in memory
    vmaUnmapMemory(m_allocator, buffer);
}
