/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef GRAPHICSPIPELINE_H
#define GRAPHICSPIPELINE_H

#include <string>
#include <vector>
#include <array>
#include "PhysicalDevice.h"
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class Shader;

    class RENGINE_API GraphicsPipeline
    {
    public:
        GraphicsPipeline();
        GraphicsPipeline(VkDevice device, std::vector<Shader*> shaders, VkExtent2D swapchainExtent, VkFormat swapchainImageFormat, VkDescriptorSetLayout descriptorSetLayout, VkFormat depthFormat);
        virtual ~GraphicsPipeline(void);

        /* */
        bool create();

        /* */
        VkRenderPass renderPass();

        /* */
        VkPipeline pipeline();

        /* */
        VkPipelineLayout layout();

        /* */
        VkPipelineBindPoint bindpoint();

    private:
        /* all of the structures that define the fixed-function stages of the pipeline,
           like input assembly, rasterizer, viewport and color blending */
        void createFixedFunctions();

        /* uniform and push values referenced by the shader that can be updated at draw time */
        void createLayout();

        /* Tell Vulkan about the framebuffer attachments that will be used while rendering.
           We need to specify how many color and depth buffers there will be, how many samples
           to use for each of them and how their contents should be handled throughout the
           rendering operations */
        void createRenderPasses();

        /* the shader modules that define the functionality of the programmable stages of the graphics pipeline */
        void createShaderStages();

        /* */
        std::vector<Shader*> m_shaders;

        /* */
        VkDevice m_device;

        /* */
        VkPipeline m_graphicsPipeline;

        /* */
        VkGraphicsPipelineCreateInfo m_pipelineInfo;

        /* */
        VkPipelineLayout m_pipelineLayout;

        /* */
        VkPipelineLayoutCreateInfo m_pipelineLayoutInfo;

        /* */
        VkRenderPass m_renderPass;

        /* */
        VkRenderPassCreateInfo m_renderPassInfo;

        /* */
        VkPipelineVertexInputStateCreateInfo m_vertexInputInfo;

        /* */
        VkPipelineInputAssemblyStateCreateInfo m_inputAssembly;

        /* */
        VkViewport m_viewport;

        /* */
        VkRect2D m_scissor;

        /* */
        std::vector<VkDynamicState> m_dynamicStates;

        /* */
        VkPipelineDynamicStateCreateInfo m_dynamicState;

        /* */
        VkPipelineViewportStateCreateInfo m_viewportState;

        /* */
        VkPipelineRasterizationStateCreateInfo m_rasterizer;

        /* */
        VkPipelineMultisampleStateCreateInfo m_multisampling;

        /* */
        VkPipelineDepthStencilStateCreateInfo m_depthStencil;

        /* */
        VkPipelineColorBlendAttachmentState m_colorBlendAttachment;

        /* */
        VkPipelineColorBlendStateCreateInfo m_colorBlending;

        /* */
        VkPipelineTessellationStateCreateInfo m_tessellation;

        /* */
        VkPipeline m_basePipelineHandle;

        /* */
        int32_t m_basePipelineIndex;

        /* */
        VkExtent2D m_swapchainExtent;
        
        /* */
        VkFormat m_swapchainImageFormat;

        /* */
        VkPipelineCache m_pipelineCache;

        /* */
        uint32_t m_createInfoCount;

        /* */
        uint32_t m_pipelineInfoCount;

        /* */
        VkPipelineShaderStageCreateInfo* m_shaderStages;

        /* */
        uint32_t m_subpass;

        /* */
        VkPipelineBindPoint m_pipelineBindPoint;

        /* */
        VkDescriptorSetLayout m_descriptorSetLayout;

        /* */
        VkFormat m_depthFormat;

        /* creation type */
        VkStructureType m_sType;

        /* Pointer to extension structure */
        const void* m_pNext;

        /* instance creation flags */
        VkInstanceCreateFlags m_flags;

        /* */
        bool m_created;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
}

#endif // GRAPHICSPIPELINE_H