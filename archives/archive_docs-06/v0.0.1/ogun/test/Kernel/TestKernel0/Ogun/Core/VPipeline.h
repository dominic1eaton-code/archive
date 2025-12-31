/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VGraphicsPipeline_h
#define VGraphicsPipeline_h

#include "VObject.h"
#include "VShader.h"
#include <vector>
#include <string>

namespace ogun
{

class VGraphicsPipeline : public VObject<VGraphicsPipeline>
{
public:
    VGraphicsPipeline();
    
    virtual ~VGraphicsPipeline(void) = default;

    VkPipeline pipeline() const { return m_pipeline; }
    
    VGraphicsPipeline& pass(VkRenderPass pass);

    VGraphicsPipeline& device(VkDevice device);
 
    VGraphicsPipeline& extent(VkExtent2D extent);
 
    VGraphicsPipeline& layout(VkDescriptorSetLayout layout);
    
    VGraphicsPipeline& shaders(std::vector<VShader> shaders);
    
    VGraphicsPipeline& samples(VkSampleCountFlagBits msaaSamples);

    VGraphicsPipeline& build();
    
    VkPipelineLayout pipelineLayout() const { return m_pipelineLayout; }

private:

    void populateFixedFunctions();

    void populateLayout();

    void populateRenderPasses();

    void populateShaderStages();

    void populateVertexInput();

    VkSampleCountFlagBits m_msaaSamples;

    /* */
    VkRenderPass m_renderPass;

    /* */
    std::vector<VShader> m_shaders;

    /* */
    VkGraphicsPipelineCreateInfo m_createInfo;

    /* */
    VkDevice m_device;

    /* */
    VkPipeline m_pipeline;

    /* */
    VkPipelineLayout m_pipelineLayout;

    /* */
    VkPipelineLayoutCreateInfo m_pipelineLayoutInfo;

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
    VkPipelineCache m_pipelineCache;

    /* */
    uint32_t m_createInfoCount;

    /* */
    VkPipelineShaderStageCreateInfo* m_shaderStages;

    /* */
    uint32_t m_subpass;

    /* */
    VkPipelineBindPoint m_pipelineBindPoint;

    /* */
    VkDescriptorSetLayout m_descriptorSetLayout;


};

} // namespace ogun

#endif // VGraphicsPipeline_h