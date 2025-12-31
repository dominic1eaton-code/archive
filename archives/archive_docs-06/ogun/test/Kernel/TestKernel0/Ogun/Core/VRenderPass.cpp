/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VRenderPass.h"
#include <array>

using namespace ogun;

VRenderPass::VRenderPass()
    : m_pipelineBindPoint(VK_PIPELINE_BIND_POINT_GRAPHICS)
{}


VRenderPass& VRenderPass::bindpoint(VkPipelineBindPoint bpoint)
{
    m_pipelineBindPoint = bpoint;
    return *this;
}

VRenderPass& VRenderPass::device(VkDevice device)
{
    m_device = device;
    return *this;
}

VRenderPass& VRenderPass::format(VkFormat format)
{
    m_imageFormat = format;
    return *this;
}

VRenderPass& VRenderPass::depth(VkFormat depth)
{
    m_depthFormat = depth;
    return *this;
}


VRenderPass& VRenderPass::samples(VkSampleCountFlagBits samples)
{
    m_msaaSamples = samples;
    return *this;
}

VRenderPass& VRenderPass::build()
{

    /* Attachment description */
    /* color */
    // In our case we'll have just a single color buffer attachment 
    // represented by one of the images from the swap chain.
    VkAttachmentDescription colorAttachment{};

    // The format of the color attachment should match the format of the
    // swap chain images, and we're not doing anything with multisampling yet, 
    // so we'll stick to 1 sample.
    colorAttachment.format = m_imageFormat;
    colorAttachment.samples = m_msaaSamples;

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
    colorAttachment.finalLayout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    /* depth */
    // The format should be the same as the depth image itself. This time we don't care about storing the depth data
    // (storeOp), because it will not be used after drawing has finished. This may allow the hardware to perform additional
    // optimizations. Just like the color buffer, we don't care about the previous depth contents, so we can use
    // VK_IMAGE_LAYOUT_UNDEFINED as initialLayout.
    VkAttachmentDescription depthAttachment{};
    depthAttachment.format = m_depthFormat;
    depthAttachment.samples = m_msaaSamples;
    depthAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    depthAttachment.storeOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    depthAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    depthAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    depthAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    depthAttachment.finalLayout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;

    VkAttachmentDescription colorAttachmentResolve{};
    colorAttachmentResolve.format = m_imageFormat;
    colorAttachmentResolve.samples = VK_SAMPLE_COUNT_1_BIT;
    colorAttachmentResolve.loadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachmentResolve.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    colorAttachmentResolve.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachmentResolve.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    colorAttachmentResolve.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    colorAttachmentResolve.finalLayout = VK_IMAGE_LAYOUT_PRESENT_SRC_KHR;

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
    colorAttachmentRef.attachment = 0u;
    colorAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    /* depth */
    VkAttachmentReference depthAttachmentRef{};
    depthAttachmentRef.attachment = 1u;
    depthAttachmentRef.layout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;

    VkAttachmentReference colorAttachmentResolveRef{};
    colorAttachmentResolveRef.attachment = 2u;
    colorAttachmentResolveRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

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
    subpass.colorAttachmentCount = 1u;
    subpass.pColorAttachments = &colorAttachmentRef;
    subpass.pDepthStencilAttachment = &depthAttachmentRef;
    subpass.pResolveAttachments = &colorAttachmentResolveRef;
    subpass.pPreserveAttachments = NULL;

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
    dependency.dstSubpass = 0u;

    // There are two built-in dependencies that take care of the transition at the start of the render pass and at the end of the render
    // pass, but the former does not occur at the right time. It assumes that the transition occurs at the start of the pipeline, but we
    // haven't acquired the image yet at that point! There are two ways to deal with this problem. We could change the waitStages for the
    // imageAvailableSemaphore to VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT to ensure that the render passes don't begin until the image is available,
    // or we can make the render pass wait for the VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT stage. I've decided to go with the second option
    // here, because it's a good excuse to have a look at subpass dependencies and how they work.
    dependency.srcStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_LATE_FRAGMENT_TESTS_BIT;
    dependency.srcAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    dependency.dstStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_EARLY_FRAGMENT_TESTS_BIT;
    dependency.dstAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    
    // create Render pass
    std::array<VkAttachmentDescription, 3> attachments = {colorAttachment, depthAttachment, colorAttachmentResolve};
    m_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_CREATE_INFO;
    m_renderPassInfo.pNext = NULL;
    m_renderPassInfo.flags = 0u;
    m_renderPassInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
    m_renderPassInfo.pAttachments = attachments.data();
    m_renderPassInfo.subpassCount = 1u;
    m_renderPassInfo.pSubpasses = &subpass;

    // The operations that should wait on this are in the color attachment stage and involve the writing of the color attachment. These settings
    // will prevent the transition from happening until it's actually necessary (and allowed): when we want to start writing colors to it.
    m_renderPassInfo.dependencyCount = 1u;
    m_renderPassInfo.pDependencies = &dependency;

    // create vulkan object
    createVk(vkCreateRenderPass(m_device,
                                &m_renderPassInfo,
                                    nullptr,
                                &m_renderPass));
    return *this;
}
