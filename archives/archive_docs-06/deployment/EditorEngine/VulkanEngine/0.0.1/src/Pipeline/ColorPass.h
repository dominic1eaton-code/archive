/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef ColorPass_H
#define ColorPass_H

#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class GraphicsPipeline;
    class VertexBuffer;
    class IndexBuffer;
    class StageBuffer;
    class Mesh;
    class UniformBuffer;
    class ShaderStorageBuffer;

    class RENGINE_API ColorPass
    {
    public:
        ColorPass();
        ColorPass(VkDevice device, VkExtent2D swapChainExtent,  std::vector<VkFramebuffer> swapChainFramebuffers, GraphicsPipeline* pipeline, VkPhysicalDeviceMemoryProperties memoryProperties, std::vector<VkDescriptorSet> descriptorSets);
        virtual ~ColorPass(void);

        /* */
        void draw(VkCommandBuffer commandBuffer, VkCommandPool commandPool, uint32_t imageIndex, std::vector<Mesh*> meshes, VkQueue transferQueue);

        // /* */
        // std::vector<UniformBuffer*> uniformBuffers();

        /* */
        std::vector<std::vector<UniformBuffer*>> uniformBuffers();

    private:
        /* */
        void begin(VkCommandBuffer commandBuffer, uint32_t imageIndex);

        /* */
        void end(VkCommandBuffer commandBuffer);

        /* */
        void copyBuffer(VkCommandBuffer commandBuffer, VkCommandPool commandPool, VkQueue transferQueue, VkBuffer srcBuffer, VkBuffer dstBuffer, VkDeviceSize size);

        /* */
        VkDevice m_device;

        /* @todo make static data not be passed through and stored multiple objects */
        VkPhysicalDeviceMemoryProperties m_memoryProperties;

        /* */
        VertexBuffer* m_meshBuffer;

        /* */
        IndexBuffer* m_meshIndexBuffer;

        /* */
        VertexBuffer* m_lightBuffer;

        /* */
        std::vector<UniformBuffer*> m_cameraBuffers;

        /* */
        std::vector<UniformBuffer*> m_meshBuffers;

        /* */
        std::vector<UniformBuffer*> m_lightBuffers;

        /* */
        VertexBuffer* m_environmentBuffer;

        /* */
        VertexBuffer* m_terrainBuffer;

        /* */
        StageBuffer* m_stageBuffer;

        /* */
        StageBuffer* m_stageIndexBuffer;

        /* */
        VkSubpassContents m_subpassContents;

        /* */
        VkRenderPassBeginInfo m_renderPassInfo;

        /* */
        VkExtent2D m_swapChainExtent;
        
        /* */
        std::vector<VkFramebuffer> m_swapChainFramebuffers;
        
        /* */
        GraphicsPipeline* m_pipeline;

        /* */
        std::vector<VkDescriptorSet> m_descriptorSets;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
}

#endif // ColorPass_H