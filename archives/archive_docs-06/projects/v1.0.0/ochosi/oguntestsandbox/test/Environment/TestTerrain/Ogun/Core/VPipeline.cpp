/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VPipeline.h"
#include "vulkan_terrain.h"

using namespace ogun;

VRayTracingPipeline::VRayTracingPipeline()
{}

VRayTracingPipeline::~VRayTracingPipeline()
{}

VRayTracingPipeline& VRayTracingPipeline::build()
{
    // VkStructureType                                      sType;
    // const void*                                          pNext;
    // VkPipelineCreateFlags                                flags;
    // uint32_t                                             stageCount;
    // const VkPipelineShaderStageCreateInfo*               pStages;
    // uint32_t                                             groupCount;
    // const VkRayTracingShaderGroupCreateInfoKHR*          pGroups;
    // uint32_t                                             maxPipelineRayRecursionDepth;
    // const VkPipelineLibraryCreateInfoKHR*                pLibraryInfo;
    // const VkRayTracingPipelineInterfaceCreateInfoKHR*    pLibraryInterface;
    // const VkPipelineDynamicStateCreateInfo*              pDynamicState;
    // VkPipelineLayout                                     layout;
    // VkPipeline                                           basePipelineHandle;
    // int32_t                                              basePipelineIndex;

    m_createInfo.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0u;
    m_createInfo.layout = m_pipelineLayout;
    // m_createInfo.stage = ;
    // m_createInfo.basePipelineHandle = ;
    // m_createInfo.basePipelineIndex = ;

    // // create vulkan object
    // createvk(vkCreateRayTracingPipelinesKHR(m_device,
    //                                    m_pipelineCache,
    //                                    m_createInfoCount,
    //                                    &m_createInfo,
    //                                    m_allocator,
    //                                    &m_pipeline));
    return *this;
}


VComputePipeline::VComputePipeline()
    : m_pipelineCache(VK_NULL_HANDLE)
    , m_createInfoCount(1u)
    , m_allocator(nullptr)
{}

VComputePipeline::~VComputePipeline()
{}

// VComputePipeline& VComputePipeline::shaders(std::vector<VShader> shaders)
// {
//     m_shaders = shaders;
//     return *this;
// }

VComputePipeline& VComputePipeline::device(VkDevice device)
{
    m_device = device;
    return *this;
}

VComputePipeline& VComputePipeline::build()
{

    m_createInfo.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0u;
    m_createInfo.layout = m_pipelineLayout;
    // m_createInfo.stage = ;
    // m_createInfo.basePipelineHandle = ;
    // m_createInfo.basePipelineIndex = ;

    // create vulkan object
    createvk(vkCreateComputePipelines(m_device,
                                       m_pipelineCache,
                                       m_createInfoCount,
                                       &m_createInfo,
                                       m_allocator,
                                       &m_pipeline));
    return *this;
}




VGraphicsPipeline::VGraphicsPipeline()
    : m_pipelineCache(VK_NULL_HANDLE)
    , m_pipeline(VK_NULL_HANDLE)
    , m_subpass(0)
    , m_pipelineBindPoint(VK_PIPELINE_BIND_POINT_GRAPHICS)
    , m_pipelineLayout(VK_NULL_HANDLE)
    , m_pipelineLayoutInfo({})
    , m_createInfo({})
    , m_createInfoCount(1u)
    , m_renderPass(VK_NULL_HANDLE)
    , m_vertexInputInfo({})
    , m_inputAssembly({})
    , m_viewport({})
    , m_scissor({})
    , m_dynamicStates({VK_DYNAMIC_STATE_VIEWPORT, VK_DYNAMIC_STATE_SCISSOR})
    , m_dynamicState({})
    , m_viewportState({})
    , m_rasterizer({})
    , m_multisampling({})
    , m_depthStencil({})
    , m_colorBlendAttachment({})
    , m_colorBlending({})
    , m_tessellation({})
    , m_basePipelineHandle(VK_NULL_HANDLE)
    , m_basePipelineIndex(0)
    , m_polygonMode(VK_POLYGON_MODE_FILL)
    , m_patchControlPoints(4u)
{}

VGraphicsPipeline& VGraphicsPipeline::mode(VkPolygonMode mode)
{
    m_polygonMode = mode;
    return *this;
}

VGraphicsPipeline& VGraphicsPipeline::pass(VkRenderPass pass)
{
    m_renderPass = pass;
    return *this;
}

VGraphicsPipeline& VGraphicsPipeline::device(VkDevice device)
{
    m_device = device;
    return *this;
}

VGraphicsPipeline& VGraphicsPipeline::extent(VkExtent2D extent)
{
    m_extent = extent;
    return *this;
}

VGraphicsPipeline& VGraphicsPipeline::layout(VkDescriptorSetLayout layout)
{
    m_descriptorSetLayout = layout;
    return *this;
}

VGraphicsPipeline& VGraphicsPipeline::shaders(std::vector<VShader> shaders)
{
    m_shaders = shaders;
    return *this;
}

VGraphicsPipeline& VGraphicsPipeline::samples(VkSampleCountFlagBits msaaSamples)
{
    m_msaaSamples = msaaSamples;
    return *this;
}

VGraphicsPipeline& VGraphicsPipeline::build()
{
    // populateVertexInput();
    
    // // describes the format of the vertex data that will be passed to the vertex shader
    // // Bindings              : spacing between data and whether the data is per-vertex or
    // //                         per-instance (see instancing)
    // // Attribute descriptions: type of the attributes passed to the vertex shader, which
    // //                         binding to load them from and at which offset
    // m_vertexInputInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO;
    // m_vertexInputInfo.pNext = NULL;
    // m_vertexInputInfo.flags = 0;
    // // We now need to set up the graphics pipeline to accept vertex data in this format by referencing the structures in createGraphicsPipeline
    // // The pipeline is now ready to accept vertex data in the format of the vertices container and pass it on to our vertex shader.
    // // auto bindingDescription = Vertex::bindingDescription();
    // // auto attributeDescriptions = Vertex::attributeDescriptions();
    // // m_vertexInputInfo.pVertexBindingDescriptions = &bindingDescription;            // Optional
    // // m_vertexInputInfo.vertexBindingDescriptionCount = static_cast<uint32_t>(bindingDescription.size());
    // // m_vertexInputInfo.pVertexAttributeDescriptions = attributeDescriptions.data(); // Optional
    // // m_vertexInputInfo.vertexAttributeDescriptionCount = static_cast<uint32_t>(attributeDescriptions.size());
    m_vertexInputInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO;
    m_vertexInputInfo.pNext = NULL;
    m_vertexInputInfo.flags = 0u;
    auto bindingDescription = TVertex::bindingDescription();
    auto attributeDescriptions = TVertex::attributeDescription();
    m_vertexInputInfo.pVertexBindingDescriptions = bindingDescription.data();            // Optional
    m_vertexInputInfo.vertexBindingDescriptionCount = static_cast<uint32_t>(bindingDescription.size());
    m_vertexInputInfo.pVertexAttributeDescriptions = attributeDescriptions.data(); // Optional
    m_vertexInputInfo.vertexAttributeDescriptionCount = static_cast<uint32_t>(attributeDescriptions.size());

    populateFixedFunctions();

    populateLayout();

    populateShaderStages();

    populateTesselation();

    m_createInfo.sType = VK_STRUCTURE_TYPE_GRAPHICS_PIPELINE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0u;
    m_createInfo.stageCount = m_shaders.size();
    m_createInfo.pStages = m_shaderStages;
    m_createInfo.pVertexInputState = &m_vertexInputInfo;
    m_createInfo.pInputAssemblyState = &m_inputAssembly;
    m_createInfo.pViewportState = &m_viewportState;
    m_createInfo.pRasterizationState = &m_rasterizer;
    m_createInfo.pMultisampleState = &m_multisampling;
    m_createInfo.pDepthStencilState = &m_depthStencil;      // Optional (unused)
    m_createInfo.pColorBlendState = &m_colorBlending;
    m_createInfo.pDynamicState = &m_dynamicState;           // Optional
    m_createInfo.layout = m_pipelineLayout;
    m_createInfo.renderPass = m_renderPass;
    m_createInfo.subpass = m_subpass;
    m_createInfo.basePipelineHandle = m_basePipelineHandle; // Optional
    m_createInfo.basePipelineIndex = m_basePipelineIndex;   // Optional
    m_createInfo.pTessellationState = &m_tesselationState;              // Optional

    // create vulkan object
    createvk(vkCreateGraphicsPipelines(m_device,
                                       m_pipelineCache,
                                       m_createInfoCount,
                                       &m_createInfo,
                                       nullptr,
                                       &m_pipeline));
    return *this;
}

void VGraphicsPipeline::populateTesselation()
{
    // m_tesselationState.
    m_tesselationState.sType = VK_STRUCTURE_TYPE_PIPELINE_TESSELLATION_STATE_CREATE_INFO;
    m_tesselationState.pNext = NULL;
    m_tesselationState.flags = 0;
    m_tesselationState.patchControlPoints = m_patchControlPoints;
}

void VGraphicsPipeline::populateVertexInput()
{
    /* Vertex input */
    // describes the format of the vertex data that will be passed to the vertex shader
    // Bindings              : spacing between data and whether the data is per-vertex or
    //                         per-instance (see instancing)
    // Attribute descriptions: type of the attributes passed to the vertex shader, which
    //                         binding to load them from and at which offset
    m_vertexInputInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO;
    m_vertexInputInfo.pNext = NULL;
    m_vertexInputInfo.flags = 0u;
    
    // We now need to set up the graphics pipeline to accept vertex data in this format by referencing the structures in createGraphicsPipeline
    // The pipeline is now ready to accept vertex data in the format of the vertices container and pass it on to our vertex shader.
    auto bindingDescription = TVertex::bindingDescription();
    auto attributeDescriptions = TVertex::attributeDescription();
    m_vertexInputInfo.pVertexBindingDescriptions = bindingDescription.data();            // Optional
    m_vertexInputInfo.vertexBindingDescriptionCount = bindingDescription.size();
    m_vertexInputInfo.pVertexAttributeDescriptions = attributeDescriptions.data(); // Optional
    m_vertexInputInfo.vertexAttributeDescriptionCount = static_cast<uint32_t>(attributeDescriptions.size());
}

void VGraphicsPipeline::populateFixedFunctions()
{
    /* Input assembly */
    // describes two things: what kind of geometry will be drawn from the vertices 
    // and if primitive restart should be enabled. topology can have values like:
    //      VK_PRIMITIVE_TOPOLOGY_POINT_LIST    : points from vertices
    //      VK_PRIMITIVE_TOPOLOGY_LINE_LIST     : line from every 2 vertices without reuse
    //      VK_PRIMITIVE_TOPOLOGY_LINE_STRIP    : the end vertex of every line is used as start vertex for the next line
    //      VK_PRIMITIVE_TOPOLOGY_TRIANGLE_LIST : triangle from every 3 vertices without reuse
    //      VK_PRIMITIVE_TOPOLOGY_TRIANGLE_STRIP: the second and third vertex of every triangle are used as first two vertices of the next triangle
    // Normally, the vertices are loaded from the vertex buffer by index in sequential order,
    // but with an element buffer you can specify the indices to use yourself. This allows you 
    // to perform optimizations like reusing vertices. If you set the primitiveRestartEnable 
    // member to VK_TRUE, then it's possible to break up lines and triangles in the _STRIP 
    // topology modes by using a special index of 0xFFFF or 0xFFFFFFFF
    m_inputAssembly.sType = VK_STRUCTURE_TYPE_PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO;
    m_inputAssembly.pNext = NULL;
    m_inputAssembly.flags = 0u;
    m_inputAssembly.topology = VK_PRIMITIVE_TOPOLOGY_PATCH_LIST;
    // m_inputAssembly.topology = VK_PRIMITIVE_TOPOLOGY_TRIANGLE_LIST;
    m_inputAssembly.primitiveRestartEnable = VK_FALSE;

    /* Viewports and scissors */
    // Viewport(s) and scissor rectangle(s) can either be specified as a static part of the 
    // pipeline or as a dynamic state set in the command buffer. While the former is more in 
    // line with the other states it's often convenient to make viewport and scissor state 
    // dynamic as it gives you a lot more flexibility. This is very common and all implementations 
    // can handle this dynamic state without a performance penalty.
    // viewport basically describes the region of the framebuffer that the output
    // will be rendered to. This will almost always be (0, 0) to (width, height)
    m_viewport.x = 0.0f;
    m_viewport.y = 0.0f;
    m_viewport.width = (float) m_extent.width;
    m_viewport.height = (float) m_extent.height;
    m_viewport.minDepth = 0.0f;
    m_viewport.maxDepth = 1.0f;

    // While viewports define the transformation from the image to the framebuffer,
    // scissor rectangles define in which regions pixels will actually be stored.
    m_scissor.offset = {0u, 0u};
    m_scissor.extent = m_extent;

    /* Dynamic state */
    // will cause the configuration of these values to be ignored and
    // you will be able (and required) to specify the data at drawing time.
    // This results in a more flexible setup and is very common for things
    // like viewport and scissor state
    m_dynamicState.sType = VK_STRUCTURE_TYPE_PIPELINE_DYNAMIC_STATE_CREATE_INFO;
    m_dynamicState.pNext = NULL;
    m_dynamicState.flags = 0u;
    m_dynamicState.dynamicStateCount = static_cast<uint32_t>(m_dynamicStates.size());
    m_dynamicState.pDynamicStates = m_dynamicStates.data();

    // // The actual viewport(s) and scissor rectangle(s) will then later be set up at drawing time.
    // m_viewportState.sType = VK_STRUCTURE_TYPE_PIPELINE_VIEWPORT_STATE_CREATE_INFO;
    // m_viewportState.pNext = NULL;
    // m_viewportState.flags = 0u;
    // m_viewportState.viewportCount = 1u;
    // m_viewportState.scissorCount = 1u;

    // // Without dynamic state, the viewport and scissor rectangle need to be set in the pipeline using 
    // // the VkPipelineViewportStateCreateInfo struct. This makes the viewport and scissor rectangle for 
    // // this pipeline immutable. Any changes required to these values would require a new pipeline to be 
    // // created with the new values.
    VkPipelineViewportStateCreateInfo viewportState{};
    m_viewportState.sType = VK_STRUCTURE_TYPE_PIPELINE_VIEWPORT_STATE_CREATE_INFO;
    m_viewportState.viewportCount = 1;
    // m_viewportState.pViewports = &m_viewport;
    m_viewportState.scissorCount = 1;
    // m_viewportState.pScissors = &m_scissor;

    /* Rasterizer */
    // takes the geometry that is shaped by the vertices from the vertex shader and turns
    // it into fragments to be colored by the fragment shader. It also performs depth testing,
    // face culling and the scissor test, and it can be configured to output fragments that
    // ill entire polygons or just the edges (wireframe rendering).
    m_rasterizer.sType = VK_STRUCTURE_TYPE_PIPELINE_RASTERIZATION_STATE_CREATE_INFO;
    m_rasterizer.pNext = NULL;
    m_rasterizer.flags = 0u;

    // If depthClampEnable is set to VK_TRUE, then fragments that are beyond the near and far planes 
    // are clamped to them as opposed to discarding them. This is useful in some special cases like 
    // shadow maps. Using this requires enabling a GPU feature.
    m_rasterizer.depthClampEnable = VK_FALSE;

    // If m_rasterizerDiscardEnable is set to VK_TRUE, then geometry never passes through the m_rasterizer 
    // stage. This basically disables any output to the framebuffer.
    m_rasterizer.rasterizerDiscardEnable = VK_FALSE;

    // The polygonMode determines how fragments are generated for geometry. The following modes are available:
    //     VK_POLYGON_MODE_FILL : fill the area of the polygon with fragments
    //     VK_POLYGON_MODE_LINE : polygon edges are drawn as lines
    //     VK_POLYGON_MODE_POINT: polygon vertices are drawn as points
    m_rasterizer.polygonMode = m_polygonMode;
    m_rasterizer.lineWidth = 1.0f;

    // The lineWidth member is straightforward, it describes the thickness of lines in terms of number of fragments.
    // The maximum line width that is supported depends on the hardware and any line thicker than 1.0f requires you
    // to enable the wideLines GPU feature
    m_rasterizer.cullMode = VK_CULL_MODE_BACK_BIT;
    m_rasterizer.frontFace = VK_FRONT_FACE_COUNTER_CLOCKWISE;
    // m_rasterizer.frontFace = VK_FRONT_FACE_CLOCKWISE;

    // The cullMode variable determines the type of face culling to use. You can disable culling, cull the front faces,
    // cull the back faces or both. The frontFace variable specifies the vertex order for faces to be considered front-facing
    // and can be clockwise or counterclockwise.
    m_rasterizer.depthBiasEnable = VK_FALSE;
    m_rasterizer.depthBiasConstantFactor = 0.0f; // Optional
    m_rasterizer.depthBiasClamp = 0.0f;          // Optional
    m_rasterizer.depthBiasSlopeFactor = 0.0f;    // Optional

    // Configures multisampling, which is one of the ways to perform anti-aliasing. It works by combining the fragment
    // shader results of multiple polygons that rasterize to the same pixel. This mainly occurs along edges, which is also
    // where the most noticeable aliasing artifacts occur. Because it doesn't need to run the fragment shader multiple times
    // if only one polygon maps to a pixel, it is significantly less expensive than simply rendering to a higher resolution 
    // and then downscaling. Enabling it requires enabling a GPU feature.
    m_multisampling.sType = VK_STRUCTURE_TYPE_PIPELINE_MULTISAMPLE_STATE_CREATE_INFO;
    m_multisampling.pNext = NULL;
    m_multisampling.flags = 0u;
    m_multisampling.sampleShadingEnable = VK_FALSE;
    m_multisampling.rasterizationSamples = m_msaaSamples;
    m_multisampling.minSampleShading = 1.0f;          // Optional
    m_multisampling.pSampleMask = nullptr;            // Optional
    m_multisampling.alphaToCoverageEnable = VK_FALSE; // Optional
    m_multisampling.alphaToOneEnable = VK_FALSE;      // Optional

    /* Depth and stencil testing */
    m_depthStencil.sType = VK_STRUCTURE_TYPE_PIPELINE_DEPTH_STENCIL_STATE_CREATE_INFO;
    m_depthStencil.pNext = NULL;
    m_depthStencil.flags = 0u;

    // The depthTestEnable field specifies if the depth of new fragments should be compared to the depth buffer to see if they should
    // be discarded. The depthWriteEnable field specifies if the new depth of fragments that pass the depth test should actually be
    // written to the depth buffer.
    m_depthStencil.depthTestEnable = VK_TRUE;
    m_depthStencil.depthWriteEnable = VK_TRUE;
    
    // The depthCompareOp field specifies the comparison that is performed to keep or discard fragments. We're sticking to the convention
    // of lower depth = closer, so the depth of new fragments should be less.
    m_depthStencil.depthCompareOp = VK_COMPARE_OP_LESS;

    // The depthBoundsTestEnable, minDepthBounds and maxDepthBounds fields are used for the optional depth bound test. Basically, this
    // allows you to only keep fragments that fall within the specified depth range. We won't be using this functionality.
    m_depthStencil.depthBoundsTestEnable = VK_TRUE;
    m_depthStencil.minDepthBounds = 0.0f; // Optional
    m_depthStencil.maxDepthBounds = 1.0f; // Optional

    // The last three fields configure stencil buffer operations, which we also won't be using in this tutorial. If you want to use these
    // operations, then you will have to make sure that the format of the depth/stencil image contains a stencil component.
    // VkStencilOp    failOp;
    // VkStencilOp    passOp;
    // VkStencilOp    depthFailOp;
    // VkCompareOp    compareOp;
    // uint32_t       compareMask;
    // uint32_t       writeMask;
    // uint32_t       reference;
    VkStencilOpState stencilFront;
    stencilFront.failOp = VK_STENCIL_OP_ZERO;
    stencilFront.passOp = VK_STENCIL_OP_ZERO;
    stencilFront.depthFailOp = VK_STENCIL_OP_ZERO;
    stencilFront.compareOp = VK_COMPARE_OP_ALWAYS;
    stencilFront.compareMask = 0xFf;
    stencilFront.writeMask = 0xfF;
    stencilFront.reference = 1;

    VkStencilOpState stencilBack;
    stencilBack.failOp = VK_STENCIL_OP_ZERO;
    stencilBack.passOp = VK_STENCIL_OP_ZERO;
    stencilBack.depthFailOp = VK_STENCIL_OP_ZERO;
    stencilBack.compareOp = VK_COMPARE_OP_ALWAYS;
    stencilBack.compareMask = 0xFF;
    stencilBack.writeMask =  0xFF;
    stencilBack.reference = 1;

    m_depthStencil.stencilTestEnable = VK_TRUE;
    m_depthStencil.front = stencilFront;
    m_depthStencil.back = stencilBack;
    // m_depthStencil.front = {}; // Optional
    // m_depthStencil.back = {};  // Optional

    /* Color blending */
    // After a fragment shader has returned a color, it needs to be combined with the color that is already in the framebuffer.
    // This transformation is known as color blending and there are two ways to do it:
    //     - Mix the old and new value to produce a final color
    //     - Combine the old and new value using a bitwise operation
    // There are two types of structs to configure color blending. The first struct, VkPipelinem_colorBlendAttachmentState contains
    // the configuration per attached framebuffer and the second struct, VkPipelineColorBlendStateCreateInfo contains the global
    // color blending settings. If blendEnable is set to VK_FALSE, then the new color from the fragment shader is passed through unmodified.
    // Otherwise, the two mixing operations are performed to compute a new color. The resulting color is AND'd with the colorWriteMask to
    // determine which channels are actually passed through.
    m_colorBlendAttachment.colorWriteMask = VK_COLOR_COMPONENT_R_BIT | VK_COLOR_COMPONENT_G_BIT | VK_COLOR_COMPONENT_B_BIT | VK_COLOR_COMPONENT_A_BIT;
    m_colorBlendAttachment.blendEnable = VK_FALSE;
    m_colorBlendAttachment.srcColorBlendFactor = VK_BLEND_FACTOR_ONE;  // Optional
    m_colorBlendAttachment.dstColorBlendFactor = VK_BLEND_FACTOR_ZERO; // Optional
    m_colorBlendAttachment.colorBlendOp = VK_BLEND_OP_ADD;             // Optional
    m_colorBlendAttachment.srcAlphaBlendFactor = VK_BLEND_FACTOR_ONE;  // Optional
    m_colorBlendAttachment.dstAlphaBlendFactor = VK_BLEND_FACTOR_ZERO; // Optional
    m_colorBlendAttachment.alphaBlendOp = VK_BLEND_OP_ADD;             // Optional

    // // The most common way to use color blending is to implement alpha blending, where we want the new
    // // color to be blended with the old color based on its opacity. The finalColor should then be computed
    // // as follows:
    // m_colorBlendAttachment.blendEnable = VK_TRUE;
    // m_colorBlendAttachment.srcColorBlendFactor = VK_BLEND_FACTOR_SRC_ALPHA;
    // m_colorBlendAttachment.dstColorBlendFactor = VK_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA;
    // m_colorBlendAttachment.colorBlendOp = VK_BLEND_OP_ADD;
    // m_colorBlendAttachment.srcAlphaBlendFactor = VK_BLEND_FACTOR_ONE;
    // m_colorBlendAttachment.dstAlphaBlendFactor = VK_BLEND_FACTOR_ZERO;
    // m_colorBlendAttachment.alphaBlendOp = VK_BLEND_OP_ADD;

    // The second structure references the array of structures for all of the framebuffers and allows you to
    // set blend constants that you can use as blend factors in the aforementioned calculations. If you want
    // to use the second method of blending (bitwise combination), then you should set logicOpEnable to VK_TRUE.
    // The bitwise operation can then be specified in the logicOp field. Note that this will automatically disable
    // the first method, as if you had set blendEnable to VK_FALSE for every attached framebuffer! The colorWriteMask
    // will also be used in this mode to determine which channels in the framebuffer will actually be affected. It
    // is also possible to disable both modes, as we've done here, in which case the fragment colors will be written
    // to the framebuffer unmodified.
    m_colorBlending.sType = VK_STRUCTURE_TYPE_PIPELINE_COLOR_BLEND_STATE_CREATE_INFO;
    m_colorBlending.pNext = NULL;
    m_colorBlending.flags = 0u;
    m_colorBlending.logicOpEnable = VK_FALSE;
    m_colorBlending.logicOp = VK_LOGIC_OP_COPY; // Optional
    m_colorBlending.attachmentCount = 1u;
    m_colorBlending.pAttachments = &m_colorBlendAttachment;
    m_colorBlending.blendConstants[0] = 0.0f;   // Optional
    m_colorBlending.blendConstants[1] = 0.0f;   // Optional
    m_colorBlending.blendConstants[2] = 0.0f;   // Optional
    m_colorBlending.blendConstants[3] = 0.0f;   // Optional
}

void VGraphicsPipeline::populateLayout()
{
    // setup push constants
    // VkPushConstantRange renderObjectIndices;
    // renderObjectIndices.offset = 0;                                // range starts at the beginning
    // renderObjectIndices.size = sizeof(RenderObjectIndices);        // 
    // renderObjectIndices.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT; // 

    // std::vector<VkPushConstantRange> pushConstants = {renderObjectIndices};

    // You can use uniform values in shaders, which are globals similar to dynamic state variables that can be
    // changed at drawing time to alter the behavior of your shaders without having to recreate them. They are
    // commonly used to pass the transformation matrix to the vertex shader, or to create texture samplers in
    // the fragment shader.
    // These uniform values need to be specified during pipeline creation by creating a VkPipelineLayout object.
    m_pipelineLayoutInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
    m_pipelineLayoutInfo.pNext = NULL;
    m_pipelineLayoutInfo.flags = 0u;
    m_pipelineLayoutInfo.setLayoutCount = 1u;                           // Optional
    m_pipelineLayoutInfo.pSetLayouts = &m_descriptorSetLayout;          // Optional
    m_pipelineLayoutInfo.pushConstantRangeCount = 0;
    m_pipelineLayoutInfo.pPushConstantRanges = nullptr;
    // m_pipelineLayoutInfo.pushConstantRangeCount = pushConstants.size(); // Optional
    // m_pipelineLayoutInfo.pPushConstantRanges = pushConstants.data();    // Optional

    // create vulkan object
    createvk(vkCreatePipelineLayout(m_device,
                                    &m_pipelineLayoutInfo,
                                    nullptr,
                                    &m_pipelineLayout));
}

void VGraphicsPipeline::populateShaderStages()
{
    m_shaderStages = new VkPipelineShaderStageCreateInfo[m_shaders.size()];
    for (int i=0; i<m_shaders.size(); i++)
    {
        VkPipelineShaderStageCreateInfo shaderStageInfo{};
        shaderStageInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
        shaderStageInfo.pNext = NULL;
        shaderStageInfo.flags = 0u;
        shaderStageInfo.stage = m_shaders[i].stage();
        shaderStageInfo.module = m_shaders[i].shader();
        shaderStageInfo.pName = m_shaders[i].entryPoint();
        m_shaderStages[i] = shaderStageInfo;
    }
}
