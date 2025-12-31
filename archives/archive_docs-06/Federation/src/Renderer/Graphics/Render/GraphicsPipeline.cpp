/**
 * @copyright DEFAULT
 * @brief: GraphicsPipeline wrapper class
 * @note : N/A
 */

#include "GraphicsPipeline.h"
#include "Logger.h"

using namespace RenderEngine;

GraphicsPipeline::GraphicsPipeline()
    : m_logunit("GraphicsPipeline")
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();

        m_pipelineLayout = new PipelineLayout();

    /* collects the raw vertex data from the buffers you specify and may also use 
       an index buffer to repeat certain elements without having to duplicate the 
       vertex data itself */
    m_pInputAssemblyState.sType = VK_STRUCTURE_TYPE_PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO;
    m_pInputAssemblyState.pNext = m_pNext;
    m_pInputAssemblyState.flags = m_flags;
    m_pInputAssemblyState.topology = VK_PRIMITIVE_TOPOLOGY_TRIANGLE_LIST;
    m_pInputAssemblyState.primitiveRestartEnable = VK_FALSE;


    m_pVertexInputState.sType = VK_STRUCTURE_TYPE_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO;
    m_pVertexInputState.pNext = m_pNext;
    m_pVertexInputState.flags = m_flags;
    m_pVertexInputState.vertexBindingDescriptionCount = 0;
    m_pVertexInputState.pVertexBindingDescriptions = nullptr;     // Optional
    m_pVertexInputState.vertexAttributeDescriptionCount = 0;
    m_pVertexInputState.pVertexAttributeDescriptions = nullptr;   // Optional

    //
    m_viewport.x = 0.0f;
    m_viewport.y = 0.0f;
    m_viewport.width = (float) swapChainExtent.width;
    m_viewport.height = (float) swapChainExtent.height;
    m_viewport.minDepth = 0.0f;
    m_viewport.maxDepth = 1.0f;

    m_scissor.offset = {0, 0};
    m_scissor.extent = swapChainExtent;

    m_pViewportState.sType = VK_STRUCTURE_TYPE_PIPELINE_VIEWPORT_STATE_CREATE_INFO;
    m_pViewportState.pNext = m_pNext;
    m_pViewportState.flags = m_flags;
    m_pViewportState.viewportCount = 1;
    m_pViewportState.pViewports = &m_viewport;
    m_pViewportState.scissorCount = 1;
    m_pViewportState.pScissors = &m_scissor;

    /* discretizes the primitives into fragments. These are the pixel elements that
       they fill on the framebuffer. Any fragments that fall outside the screen are
       discarded and the attributes outputted by the vertex shader are interpolated
       across the fragments, as shown in the figure. Usually the fragments that are
       behind other primitive fragments are also discarded here because of depth testing */
    m_pRasterizationState.sType = VK_STRUCTURE_TYPE_PIPELINE_RASTERIZATION_STATE_CREATE_INFO;
    m_pRasterizationState.pNext =  m_pNext;
    m_pRasterizationState.flags =  m_flags;
    m_pRasterizationState.depthClampEnable = VK_FALSE;
    m_pRasterizationState.rasterizerDiscardEnable = VK_FALSE;
    m_pRasterizationState.polygonMode = VK_POLYGON_MODE_FILL;
    m_pRasterizationState.cullMode = VK_CULL_MODE_BACK_BIT;
    m_pRasterizationState.frontFace = VK_FRONT_FACE_CLOCKWISE;
    m_pRasterizationState.depthBiasEnable = VK_FALSE;
    m_pRasterizationState.depthBiasConstantFactor = 0.0f;   // Optional
    m_pRasterizationState.depthBiasClamp = 0.0f;            // Optional
    m_pRasterizationState.depthBiasSlopeFactor = 0.0f;      // Optional
    m_pRasterizationState.lineWidth = 1.0f;

    //
    m_pMultisampleState.sType = VK_STRUCTURE_TYPE_PIPELINE_MULTISAMPLE_STATE_CREATE_INFO;
    m_pMultisampleState.pNext = m_pNext;
    m_pMultisampleState.flags = m_flags;
    m_pMultisampleState.rasterizationSamples = VK_SAMPLE_COUNT_1_BIT;
    m_pMultisampleState.sampleShadingEnable = VK_FALSE;
    m_pMultisampleState.minSampleShading = 1.0f;            // Optional
    m_pMultisampleState.pSampleMask = nullptr;              // Optional
    m_pMultisampleState.alphaToCoverageEnable = VK_FALSE;   // Optional
    m_pMultisampleState.alphaToOneEnable = VK_FALSE;        // Optional

    //
    m_colorBlendAttachment.colorWriteMask = VK_COLOR_COMPONENT_R_BIT | VK_COLOR_COMPONENT_G_BIT | VK_COLOR_COMPONENT_B_BIT | VK_COLOR_COMPONENT_A_BIT;
    m_colorBlendAttachment.blendEnable = VK_TRUE;
    m_colorBlendAttachment.srcColorBlendFactor = VK_BLEND_FACTOR_SRC_ALPHA;
    m_colorBlendAttachment.dstColorBlendFactor = VK_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA;
    m_colorBlendAttachment.colorBlendOp = VK_BLEND_OP_ADD;
    m_colorBlendAttachment.srcAlphaBlendFactor = VK_BLEND_FACTOR_ONE;
    m_colorBlendAttachment.dstAlphaBlendFactor = VK_BLEND_FACTOR_ZERO;
    m_colorBlendAttachment.alphaBlendOp = VK_BLEND_OP_ADD;

    /* applies operations to mix different fragments that map to the same pixel in 
       the framebuffer. Fragments can simply overwrite each other, add up or be mixed 
       based upon transparency. */
    m_pColorBlendState.sType = VK_STRUCTURE_TYPE_PIPELINE_COLOR_BLEND_STATE_CREATE_INFO;
    m_pColorBlendState.pNext = pNext;
    m_pColorBlendState.flags = flags;
    m_pColorBlendState.logicOpEnable = VK_FALSE;
    m_pColorBlendState.logicOp = VK_LOGIC_OP_COPY;  // Optional
    m_pColorBlendState.attachmentCount = 1;
    m_pColorBlendState.pAttachments = m_colorBlendAttachment;
    m_pColorBlendState.blendConstants[0] = 0.0f;    // Optional
    m_pColorBlendState.blendConstants[1] = 0.0f;    // Optional
    m_pColorBlendState.blendConstants[2] = 0.0f;    // Optional
    m_pColorBlendState.blendConstants[3] = 0.0f;    // Optional

    //
    dynamicStates[0] = VK_DYNAMIC_STATE_VIEWPORT
    dynamicStates[1] = VK_DYNAMIC_STATE_LINE_WIDTH
    m_pDynamicState.sType = VK_STRUCTURE_TYPE_PIPELINE_DYNAMIC_STATE_CREATE_INFO;
    m_pDynamicState.pNext = pNext;
    m_pDynamicState.flags = flags;
    m_pDynamicState.dynamicStateCount = 2;
    m_pDynamicState.pDynamicStates = m_dynamicStates;

    /* allow to subdivide geometry based on certain rules to increase the mesh quality.
       This is often used to make surfaces like brick walls and staircases look less flat
       when they are nearby.*/
    m_pTessellationState.sType = VK_STRUCTURE_TYPE_PIPELINE_TESSELLATION_STATE_CREATE_INFO;
    m_pTessellationState.pNext = pNext;
    m_pTessellationState.flags = flags;
    m_pTessellationState.patchControlPoints = 1;

}

GraphicsPipeline::~GraphicsPipeline() {}

bool GraphicsPipeline::create()
{
    return true;
}