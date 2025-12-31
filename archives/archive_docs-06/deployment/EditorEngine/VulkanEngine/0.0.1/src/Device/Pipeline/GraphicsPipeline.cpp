/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "GraphicsPipeline.h"
#include "Logger.h"
#include "VulkanCommon.h"
#include "Shader.h"
#include "Math/Vertex.h"
#include <array>

using namespace RenderEngine;

GraphicsPipeline::GraphicsPipeline()
{}

GraphicsPipeline::GraphicsPipeline(VkDevice device, std::vector<Shader*> shaders, VkExtent2D swapchainExtent, VkFormat swapchainImageFormat, VkDescriptorSetLayout descriptorSetLayout, VkFormat depthFormat)
    : m_logunit("GraphicsPipeline")
    , m_device(device)
    , m_shaders(shaders)
    , m_swapchainExtent(swapchainExtent)
    , m_swapchainImageFormat(swapchainImageFormat)
    , m_graphicsPipeline(VK_NULL_HANDLE)
    , m_pipelineInfo({})
    , m_pipelineLayout(VK_NULL_HANDLE)
    , m_pipelineLayoutInfo({})
    , m_pipelineInfoCount(1)
    , m_renderPass(VK_NULL_HANDLE)
    , m_renderPassInfo({})
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
    , m_basePipelineIndex(-1)
    , m_created(false)
    , m_pipelineCache(VK_NULL_HANDLE)
    , m_subpass(0)
    , m_pipelineBindPoint(VK_PIPELINE_BIND_POINT_GRAPHICS)
    , m_sType(VK_STRUCTURE_TYPE_GRAPHICS_PIPELINE_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_descriptorSetLayout(descriptorSetLayout)
    , m_depthFormat(depthFormat)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    create();
}

GraphicsPipeline::~GraphicsPipeline()
{
    vkDestroyPipeline(m_device, m_graphicsPipeline, nullptr);
    vkDestroyPipelineLayout(m_device, m_pipelineLayout, nullptr);
    vkDestroyRenderPass(m_device, m_renderPass, nullptr);
}

bool GraphicsPipeline::create()
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Creating graphics pipeline " << LoggingTool::Logger::endl;
    
    /* Fixed pipeline functions */
    createFixedFunctions();

    /* Pipeline layout */
    createLayout();

    /* Render Passes */
    createRenderPasses();

    /* Shader Stages */
    createShaderStages();

    /* @temp static data changing */
    /* Vertex input */
    // describes the format of the vertex data that will be passed to the vertex shader
    // Bindings              : spacing between data and whether the data is per-vertex or
    //                         per-instance (see instancing)
    // Attribute descriptions: type of the attributes passed to the vertex shader, which
    //                         binding to load them from and at which offset
    m_vertexInputInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO;

    // We now need to set up the graphics pipeline to accept vertex data in this format by referencing the structures in createGraphicsPipeline
    // The pipeline is now ready to accept vertex data in the format of the vertices container and pass it on to our vertex shader.
    auto bindingDescription = Vertex::bindingDescription();
    auto attributeDescriptions = Vertex::attributeDescriptions();
    m_vertexInputInfo.pVertexBindingDescriptions = &bindingDescription;            // Optional
    m_vertexInputInfo.vertexBindingDescriptionCount = 1;
    m_vertexInputInfo.pVertexAttributeDescriptions = attributeDescriptions.data(); // Optional
    m_vertexInputInfo.vertexAttributeDescriptionCount = static_cast<uint32_t>(attributeDescriptions.size());
    /* @temp static data changing */

    // create grapics pipelines object
    m_pipelineInfo.sType = m_sType;
    m_pipelineInfo.pNext = m_pNext;
    m_pipelineInfo.flags = m_flags;
    m_pipelineInfo.stageCount = m_shaders.size();
    m_pipelineInfo.pStages = m_shaderStages;
    m_pipelineInfo.pVertexInputState = &m_vertexInputInfo;
    m_pipelineInfo.pInputAssemblyState = &m_inputAssembly;
    m_pipelineInfo.pViewportState = &m_viewportState;
    m_pipelineInfo.pRasterizationState = &m_rasterizer;
    m_pipelineInfo.pMultisampleState = &m_multisampling;
    m_pipelineInfo.pDepthStencilState = &m_depthStencil;      // Optional (unused)
    m_pipelineInfo.pColorBlendState = &m_colorBlending;
    m_pipelineInfo.pDynamicState = &m_dynamicState;           // Optional
    m_pipelineInfo.layout = m_pipelineLayout;
    m_pipelineInfo.renderPass = m_renderPass;
    m_pipelineInfo.subpass = m_subpass;
    m_pipelineInfo.basePipelineHandle = m_basePipelineHandle; // Optional
    m_pipelineInfo.basePipelineIndex = m_basePipelineIndex;   // Optional
    m_pipelineInfo.pTessellationState = nullptr;              // Optional

    // create vulkan object
    m_created = Utilities::checkVKCreation(vkCreateGraphicsPipelines(m_device,
                                                                     m_pipelineCache,
                                                                     m_pipelineInfoCount,
                                                                    &m_pipelineInfo,
                                                                     nullptr,
                                                                    &m_graphicsPipeline));
    return m_created;
}

VkRenderPass GraphicsPipeline::renderPass()
{
    return m_renderPass;
}

VkPipeline GraphicsPipeline::pipeline()
{
    return m_graphicsPipeline;
}

VkPipelineLayout GraphicsPipeline::layout()
{
    return m_pipelineLayout;
}

VkPipelineBindPoint GraphicsPipeline::bindpoint()
{
    return m_pipelineBindPoint;
}

void GraphicsPipeline::createFixedFunctions()
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
    m_inputAssembly.topology = VK_PRIMITIVE_TOPOLOGY_TRIANGLE_LIST;
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
    m_viewport.width = (float) m_swapchainExtent.width;
    m_viewport.height = (float) m_swapchainExtent.height;
    m_viewport.minDepth = 0.0f;
    m_viewport.maxDepth = 1.0f;

    // While viewports define the transformation from the image to the framebuffer,
    // scissor rectangles define in which regions pixels will actually be stored.
    m_scissor.offset = {0, 0};
    m_scissor.extent = m_swapchainExtent;

    /* Dynamic state */
    // will cause the configuration of these values to be ignored and
    // you will be able (and required) to specify the data at drawing time.
    // This results in a more flexible setup and is very common for things
    // like viewport and scissor state
    m_dynamicState.sType = VK_STRUCTURE_TYPE_PIPELINE_DYNAMIC_STATE_CREATE_INFO;
    m_dynamicState.dynamicStateCount = static_cast<uint32_t>(m_dynamicStates.size());
    m_dynamicState.pDynamicStates = m_dynamicStates.data();

    // The actual viewport(s) and scissor rectangle(s) will then later be set up at drawing time.
    m_viewportState.sType = VK_STRUCTURE_TYPE_PIPELINE_VIEWPORT_STATE_CREATE_INFO;
    m_viewportState.viewportCount = 1;
    m_viewportState.scissorCount = 1;

    // Without dynamic state, the viewport and scissor rectangle need to be set in the pipeline using 
    // the VkPipelineViewportStateCreateInfo struct. This makes the viewport and scissor rectangle for 
    // this pipeline immutable. Any changes required to these values would require a new pipeline to be 
    // created with the new values.
    // VkPipelineViewportStateCreateInfo viewportState{};
    // viewportState.sType = VK_STRUCTURE_TYPE_PIPELINE_VIEWPORT_STATE_CREATE_INFO;
    // viewportState.viewportCount = 1;
    // viewportState.pViewports = &viewport;
    // viewportState.scissorCount = 1;
    // viewportState.pScissors = &scissor;

    /* Rasterizer */
    // takes the geometry that is shaped by the vertices from the vertex shader and turns
    // it into fragments to be colored by the fragment shader. It also performs depth testing,
    // face culling and the scissor test, and it can be configured to output fragments that
    // ill entire polygons or just the edges (wireframe rendering).
    m_rasterizer.sType = VK_STRUCTURE_TYPE_PIPELINE_RASTERIZATION_STATE_CREATE_INFO;

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
    m_rasterizer.polygonMode = VK_POLYGON_MODE_FILL;
    m_rasterizer.lineWidth = 1.0f;

    // The lineWidth member is straightforward, it describes the thickness of lines in terms of number of fragments.
    // The maximum line width that is supported depends on the hardware and any line thicker than 1.0f requires you
    // to enable the wideLines GPU feature
    m_rasterizer.cullMode = VK_CULL_MODE_BACK_BIT;
    m_rasterizer.frontFace = VK_FRONT_FACE_COUNTER_CLOCKWISE;

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
    m_multisampling.sampleShadingEnable = VK_FALSE;
    m_multisampling.rasterizationSamples = VK_SAMPLE_COUNT_1_BIT;
    m_multisampling.minSampleShading = 1.0f;          // Optional
    m_multisampling.pSampleMask = nullptr;            // Optional
    m_multisampling.alphaToCoverageEnable = VK_FALSE; // Optional
    m_multisampling.alphaToOneEnable = VK_FALSE;      // Optional

    /* Depth and stencil testing */
    m_depthStencil.sType = VK_STRUCTURE_TYPE_PIPELINE_DEPTH_STENCIL_STATE_CREATE_INFO;

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
    m_depthStencil.depthBoundsTestEnable = VK_FALSE;
    m_depthStencil.minDepthBounds = 0.0f; // Optional
    m_depthStencil.maxDepthBounds = 1.0f; // Optional

    // The last three fields configure stencil buffer operations, which we also won't be using in this tutorial. If you want to use these
    // operations, then you will have to make sure that the format of the depth/stencil image contains a stencil component.
    m_depthStencil.stencilTestEnable = VK_FALSE;
    m_depthStencil.front = {}; // Optional
    m_depthStencil.back = {};  // Optional

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

    // The most common way to use color blending is to implement alpha blending, where we want the new
    // color to be blended with the old color based on its opacity. The finalColor should then be computed
    // as follows:
    m_colorBlendAttachment.blendEnable = VK_TRUE;
    m_colorBlendAttachment.srcColorBlendFactor = VK_BLEND_FACTOR_SRC_ALPHA;
    m_colorBlendAttachment.dstColorBlendFactor = VK_BLEND_FACTOR_ONE_MINUS_SRC_ALPHA;
    m_colorBlendAttachment.colorBlendOp = VK_BLEND_OP_ADD;
    m_colorBlendAttachment.srcAlphaBlendFactor = VK_BLEND_FACTOR_ONE;
    m_colorBlendAttachment.dstAlphaBlendFactor = VK_BLEND_FACTOR_ZERO;
    m_colorBlendAttachment.alphaBlendOp = VK_BLEND_OP_ADD;

    // The second structure references the array of structures for all of the framebuffers and allows you to
    // set blend constants that you can use as blend factors in the aforementioned calculations. If you want
    // to use the second method of blending (bitwise combination), then you should set logicOpEnable to VK_TRUE.
    // The bitwise operation can then be specified in the logicOp field. Note that this will automatically disable
    // the first method, as if you had set blendEnable to VK_FALSE for every attached framebuffer! The colorWriteMask
    // will also be used in this mode to determine which channels in the framebuffer will actually be affected. It
    // is also possible to disable both modes, as we've done here, in which case the fragment colors will be written
    // to the framebuffer unmodified.
    m_colorBlending.sType = VK_STRUCTURE_TYPE_PIPELINE_COLOR_BLEND_STATE_CREATE_INFO;
    m_colorBlending.logicOpEnable = VK_FALSE;
    m_colorBlending.logicOp = VK_LOGIC_OP_COPY; // Optional
    m_colorBlending.attachmentCount = 1;
    m_colorBlending.pAttachments = &m_colorBlendAttachment;
    m_colorBlending.blendConstants[0] = 0.0f;   // Optional
    m_colorBlending.blendConstants[1] = 0.0f;   // Optional
    m_colorBlending.blendConstants[2] = 0.0f;   // Optional
    m_colorBlending.blendConstants[3] = 0.0f;   // Optional
}

void GraphicsPipeline::createLayout()
{
    // setup push constants
    VkPushConstantRange renderObjectIndices;
    renderObjectIndices.offset = 0;                                // range starts at the beginning
    renderObjectIndices.size = sizeof(RenderObjectIndices);        // 
    renderObjectIndices.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT; // 

    std::vector<VkPushConstantRange> pushConstants = {renderObjectIndices};

    // You can use uniform values in shaders, which are globals similar to dynamic state variables that can be
    // changed at drawing time to alter the behavior of your shaders without having to recreate them. They are
    // commonly used to pass the transformation matrix to the vertex shader, or to create texture samplers in
    // the fragment shader.
    // These uniform values need to be specified during pipeline creation by creating a VkPipelineLayout object.
    m_pipelineLayoutInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
    m_pipelineLayoutInfo.setLayoutCount = 1;                            // Optional
    m_pipelineLayoutInfo.pSetLayouts = &m_descriptorSetLayout;          // Optional
    m_pipelineLayoutInfo.pushConstantRangeCount = pushConstants.size(); // Optional
    m_pipelineLayoutInfo.pPushConstantRanges = pushConstants.data();    // Optional

    // create vulkan object
    Utilities::checkVKCreation(vkCreatePipelineLayout(m_device,
                                                     &m_pipelineLayoutInfo,
                                                      nullptr,
                                                     &m_pipelineLayout));
}

void GraphicsPipeline::createRenderPasses()
{
    /* Attachment description */
    /* color */
    // In our case we'll have just a single color buffer attachment 
    // represented by one of the images from the swap chain.
    VkAttachmentDescription colorAttachment{};

    // The format of the color attachment should match the format of the
    // swap chain images, and we're not doing anything with multisampling yet, 
    // so we'll stick to 1 sample.
    colorAttachment.format = m_swapchainImageFormat;
    colorAttachment.samples = VK_SAMPLE_COUNT_1_BIT;

    // The loadOp and storeOp apply to color and depth data, and stencilLoadOp / stencilStoreOp apply to stencil data.
    // The loadOp and storeOp determine what to do with the data in the attachment before 
    // rendering and after rendering. We have the following choices for loadOp:
    //     VK_ATTACHMENT_LOAD_OP_LOAD     : Preserve the existing contents of the attachment
    //     VK_ATTACHMENT_LOAD_OP_CLEAR    : Clear the values to a constant at the start
    //     VK_ATTACHMENT_LOAD_OP_DONT_CARE: Existing contents are undefined; we don't care about them
    colorAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    colorAttachment.storeOp = VK_ATTACHMENT_STORE_OP_STORE;

    // In our case we're going to use the clear operation to clear the framebuffer to black 
    // before drawing a new frame. There are only two possibilities for the storeOp:
    //     VK_ATTACHMENT_STORE_OP_STORE    : Rendered contents will be stored in memory and can be read later
    //     VK_ATTACHMENT_STORE_OP_DONT_CARE: Contents of the framebuffer will be undefined after the rendering operation
    colorAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;

    // Textures and framebuffers in Vulkan are represented by VkImage objects with a certain pixel
    // format, however the layout of the pixels in memory can change based on what you're trying to
    // do with an image.
    // Some of the most common layouts are:
    //     VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL: Images used as color attachment
    //     VK_IMAGE_LAYOUT_PRESENT_SRC_KHR: Images to be presented in the swap chain
    //     VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL: Images to be used as destination for a memory copy operation
    // The initialLayout specifies which layout the image will have before the render pass begins. The
    // finalLayout specifies the layout to automatically transition to when the render pass finishes. Using
    // VK_IMAGE_LAYOUT_UNDEFINED for initialLayout means that we don't care what previous layout the image was
    // in. The caveat of this special value is that the contents of the image are not guaranteed to be preserved,
    // but that doesn't matter since we're going to clear it anyway. We want the image to be ready for presentation
    // using the swap chain after rendering, which is why we use VK_IMAGE_LAYOUT_PRESENT_SRC_KHR as finalLayout.
    colorAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    colorAttachment.finalLayout = VK_IMAGE_LAYOUT_PRESENT_SRC_KHR;

    /* depth */
    // The format should be the same as the depth image itself. This time we don't care about storing the depth data
    // (storeOp), because it will not be used after drawing has finished. This may allow the hardware to perform additional
    // optimizations. Just like the color buffer, we don't care about the previous depth contents, so we can use
    // VK_IMAGE_LAYOUT_UNDEFINED as initialLayout.
    VkAttachmentDescription depthAttachment{};
    depthAttachment.format = m_depthFormat;
    depthAttachment.samples = VK_SAMPLE_COUNT_1_BIT;
    depthAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    depthAttachment.storeOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    depthAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    depthAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    depthAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    depthAttachment.finalLayout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;

    /* Subpasses and attachment references */
    /* color */
    // A single render pass can consist of multiple subpasses. Subpasses are subsequent rendering operations that
    // depend on the contents of framebuffers in previous passes, for example a sequence of post-processing effects
    // that are applied one after another. If you group these rendering operations into one render pass, then Vulkan
    // is able to reorder the operations and conserve memory bandwidth for possibly better performance.
    // Every subpass references one or more of the attachments that we've described using the structure in the previous sections.
    VkAttachmentReference colorAttachmentRef{};

    // The attachment parameter specifies which attachment to reference by its index in the attachment descriptions array.
    // Our array consists of a single VkAttachmentDescription, so its index is 0. The layout specifies which layout we would
    // like the attachment to have during a subpass that uses this reference. Vulkan will automatically transition the attachment
    // to this layout when the subpass is started. We intend to use the attachment to function as a color buffer and the
    // VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL layout will give us the best performance, as its name implies
    colorAttachmentRef.attachment = 0;
    colorAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    /* depth */
    VkAttachmentReference depthAttachmentRef{};
    depthAttachmentRef.attachment = 1;
    depthAttachmentRef.layout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;

    // Vulkan may also support compute subpasses in the future, so we have to be explicit about this being a graphics subpass
    VkSubpassDescription subpass{};
    subpass.pipelineBindPoint = m_pipelineBindPoint;

    // The index of the attachment in this array is directly referenced from the fragment shader with the layout(location = 0)
    // out vec4 outColor directive!
    // The following other types of attachments can be referenced by a subpass:
    //     pInputAttachments      : Attachments that are read from a shader
    //     pResolveAttachments    : Attachments used for multisampling color attachments
    //     pDepthStencilAttachment: Attachment for depth and stencil data
    //     pPreserveAttachments   : Attachments that are not used by this subpass, but for which the data must be preserved
    subpass.colorAttachmentCount = 1;
    subpass.pColorAttachments = &colorAttachmentRef;
    subpass.pDepthStencilAttachment = &depthAttachmentRef;

    // Subpass dependencies
    //      subpasses in a render pass automatically take care of
    //      image layout transitions. These transitions are controlled
    //      by subpass dependencies, which specify memory and execution
    //      dependencies between subpasses
    VkSubpassDependency dependency{};

    // The first two fields specify the indices of the dependency and the dependent subpass. The special value VK_SUBPASS_EXTERNAL refers
    // to the implicit subpass before or after the render pass depending on whether it is specified in srcSubpass or dstSubpass. The index
    // 0 refers to our subpass, which is the first and only one. The dstSubpass must always be higher than srcSubpass to prevent cycles in
    // the dependency graph (unless one of the subpasses is VK_SUBPASS_EXTERNAL).
    dependency.srcSubpass = VK_SUBPASS_EXTERNAL;
    dependency.dstSubpass = 0;

    // There are two built-in dependencies that take care of the transition at the start of the render pass and at the end of the render
    // pass, but the former does not occur at the right time. It assumes that the transition occurs at the start of the pipeline, but we
    // haven't acquired the image yet at that point! There are two ways to deal with this problem. We could change the waitStages for the
    // imageAvailableSemaphore to VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT to ensure that the render passes don't begin until the image is available,
    // or we can make the render pass wait for the VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT stage. I've decided to go with the second option
    // here, because it's a good excuse to have a look at subpass dependencies and how they work.
    dependency.srcStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_EARLY_FRAGMENT_TESTS_BIT;
    dependency.srcAccessMask = 0;
    dependency.dstStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_EARLY_FRAGMENT_TESTS_BIT;
    dependency.dstAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    
    // create Render pass
    std::array<VkAttachmentDescription, 2> attachments = {colorAttachment, depthAttachment};
    m_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_CREATE_INFO;
    m_renderPassInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
    m_renderPassInfo.pAttachments = attachments.data();
    m_renderPassInfo.subpassCount = 1;
    m_renderPassInfo.pSubpasses = &subpass;

    // The operations that should wait on this are in the color attachment stage and involve the writing of the color attachment. These settings
    // will prevent the transition from happening until it's actually necessary (and allowed): when we want to start writing colors to it.
    m_renderPassInfo.dependencyCount = 1;
    m_renderPassInfo.pDependencies = &dependency;

    // create vulkan object
    bool created = Utilities::checkVKCreation(vkCreateRenderPass(m_device,
                                                                &m_renderPassInfo,
                                                                 nullptr,
                                                                &m_renderPass));
}

void GraphicsPipeline::createShaderStages()
{
    m_shaderStages = new VkPipelineShaderStageCreateInfo[m_shaders.size()];
    for (int i=0; i<m_shaders.size(); i++)
    {
        VkPipelineShaderStageCreateInfo shaderStageInfo{};
        shaderStageInfo.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
        shaderStageInfo.stage = m_shaders[i]->stage();
        shaderStageInfo.module = m_shaders[i]->shader();
        shaderStageInfo.pName = m_shaders[i]->entryPoint();
        m_shaderStages[i] = shaderStageInfo;
    }
}
