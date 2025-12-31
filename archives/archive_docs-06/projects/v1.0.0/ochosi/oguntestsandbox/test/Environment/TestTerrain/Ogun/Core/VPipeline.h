/**
 * @header
 * @copyright
 * @brief Vulkan Pipelines
 * @note 
 */

#pragma once
#ifndef VPipeline_h
#define VPipeline_h

#include "VObject.h"
#include "VShader.h"
#include <vector>
#include <string>

namespace ogun
{


class VRayTracingPipeline : public VObject<VRayTracingPipeline>
{
public:
    VRayTracingPipeline();
        
    virtual ~VRayTracingPipeline(void);

    /**
     * populate logical device
     * @return reference to this object
     */
    VRayTracingPipeline& device(VkDevice device);

    /**
     * build vulkan object
     * @return reference to this object
     */
    VRayTracingPipeline& build();

private:
    /**
     * create info
     */
    VkRayTracingPipelineCreateInfoKHR m_createInfo;

    /**
     * logical device
     */
    VkDevice m_device;

    /**
     * 
     */
    VkPipelineCache m_pipelineCache;

    /**
     * 
     */
    uint32_t m_createInfoCount;

    /**
     * 
     */
    VkDescriptorSetLayout m_descriptorLayout;
    
    /**
     * 
     */
    VkPipelineLayout m_pipelineLayout;
    
    /**
     * 
     */
    VkPipeline m_pipeline;
};    


class VComputePipeline : public VObject<VComputePipeline>
{
public:
    VComputePipeline();
        
    virtual ~VComputePipeline(void);

    /**
     * populate logical device
     * @return reference to this object
     */
    VComputePipeline& device(VkDevice device);

    /**
     * build vulkan object
     * @return reference to this object
     */
    VComputePipeline& build();

private:
    /**
     * create info
     */
    VkComputePipelineCreateInfo m_createInfo;

    /**
     * logical device
     */
    VkDevice m_device;

    /**
     * 
     */
    VkPipelineCache m_pipelineCache;

    /**
     * 
     */
    uint32_t m_createInfoCount;

    /**
     * 
     */
    const VkAllocationCallbacks* m_allocator;
    
    /**
     * 
     */
    VkDescriptorSetLayout m_descriptorLayout;
    
    /**
     * 
     */
    VkPipelineLayout m_pipelineLayout;
    
    /**
     * 
     */
    VkPipeline m_pipeline;
};


class VGraphicsPipeline : public VObject<VGraphicsPipeline>
{
public:
    VGraphicsPipeline();
    
    virtual ~VGraphicsPipeline(void) = default;

    /**
     * get pipeline layout
     * @return pipeline layout
     */
    VkPipelineLayout pipelineLayout() const { return m_pipelineLayout; }
    
    /**
     * get pipeline
     * @return pipeline
     */
    VkPipeline pipeline() const { return m_pipeline; }
    
    /**
     * populate render pass
     * @return reference to this object
     */
    VGraphicsPipeline& pass(VkRenderPass pass);

    /**
     * populate logical device
     * @return reference to this object
     */
    VGraphicsPipeline& device(VkDevice device);
 
    /**
     * populate draw window extent
     * @return reference to this object
     */
    VGraphicsPipeline& extent(VkExtent2D extent);
 
    /**
     * populate descriptor layout
     * @return reference to this object
     */
    VGraphicsPipeline& layout(VkDescriptorSetLayout layout);
    
    /**
     * populate shaders
     * @return reference to this object
     */
    VGraphicsPipeline& shaders(std::vector<VShader> shaders);
    
    /**
     * populate MSAA samples
     * @return reference to this object
     */
    VGraphicsPipeline& samples(VkSampleCountFlagBits msaaSamples);

    /**
     * populate render polygon mode
     * @return reference to this object
     */
    VGraphicsPipeline& mode(VkPolygonMode mode);

    /**
     * build vulkan object
     * @return reference to this object
     */
    VGraphicsPipeline& build();

private:

    void populateFixedFunctions();

    void populateLayout();

    void populateRenderPasses();

    void populateShaderStages();

    void populateVertexInput();

    void populateTesselation();

    VkPipelineTessellationStateCreateInfo m_tesselationState;

    VkSampleCountFlagBits m_msaaSamples;

    uint8_t m_patchControlPoints;

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
    VkExtent2D m_extent;

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

    VkPolygonMode m_polygonMode;
};

} // namespace ogun

#endif // VPipeline_h