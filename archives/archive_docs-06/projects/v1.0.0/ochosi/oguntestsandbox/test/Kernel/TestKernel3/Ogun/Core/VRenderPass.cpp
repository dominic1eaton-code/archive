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

VRenderPass& VRenderPass::buildOffscreen()
{
    /* Attachment description */
    /* color */
    VkAttachmentDescription colorAttachment{};
    colorAttachment.format = m_imageFormat;
    colorAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    colorAttachment.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    colorAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    colorAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    colorAttachment.finalLayout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;
    colorAttachment.samples = VK_SAMPLE_COUNT_1_BIT;

    /* primitiveID */
    VkAttachmentDescription primitiveIDAttachment{};
    primitiveIDAttachment.format = m_imageFormat; //VK_FORMAT_R8_UINT;
    primitiveIDAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    primitiveIDAttachment.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    primitiveIDAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    primitiveIDAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    primitiveIDAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    primitiveIDAttachment.finalLayout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;
    primitiveIDAttachment.samples = VK_SAMPLE_COUNT_1_BIT;

    /* Subpasses and attachment references */
    /* color */
    VkAttachmentReference colorAttachmentRef{};
    colorAttachmentRef.attachment = 0u;
    colorAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    VkAttachmentReference primitiveIDAttachmentRef{};
    primitiveIDAttachmentRef.attachment = 1u;
    primitiveIDAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL; //VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;

    std::vector<VkAttachmentReference> colorAttachmentsRefs;
    colorAttachmentsRefs.push_back(colorAttachmentRef);
    colorAttachmentsRefs.push_back(primitiveIDAttachmentRef);

    // Vulkan may also support compute subpasses in the future, so we have to be explicit about this being a graphics subpass
    VkSubpassDescription subpass{};
    subpass.flags = 0;
    subpass.pipelineBindPoint = m_pipelineBindPoint;
    subpass.colorAttachmentCount = colorAttachmentsRefs.size();
    subpass.pColorAttachments = colorAttachmentsRefs.data();
    subpass.pDepthStencilAttachment = NULL;
    subpass.pResolveAttachments = NULL;
    subpass.preserveAttachmentCount = 0;
    subpass.pPreserveAttachments = NULL;
    subpass.inputAttachmentCount = 0;
    subpass.pInputAttachments = NULL;

    std::vector<VkSubpassDescription> subpasses;
    subpasses.push_back(subpass);

    // Subpass dependencies
    VkSubpassDependency dependency{};
    dependency.srcSubpass = VK_SUBPASS_EXTERNAL;
    dependency.dstSubpass = 0u;
    dependency.srcStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_LATE_FRAGMENT_TESTS_BIT;
    dependency.srcAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    dependency.dstStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_EARLY_FRAGMENT_TESTS_BIT;
    dependency.dstAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    
    // create Render pass
    std::array<VkAttachmentDescription, 2> attachments = {colorAttachment, primitiveIDAttachment};
    m_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_CREATE_INFO;
    m_renderPassInfo.pNext = NULL;
    m_renderPassInfo.flags = 0u;
    m_renderPassInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
    m_renderPassInfo.pAttachments = attachments.data();
    m_renderPassInfo.subpassCount = subpasses.size();
    m_renderPassInfo.pSubpasses = subpasses.data();
    m_renderPassInfo.dependencyCount = 1u;
    m_renderPassInfo.pDependencies = &dependency;

    // create vulkan object
    createvk(vkCreateRenderPass(m_device,
                                &m_renderPassInfo,
                                    nullptr,
                                &m_renderPass));
    return *this;
}

VRenderPass& VRenderPass::build()
{
    /* Attachment description */
    /* color */
    VkAttachmentDescription colorAttachment{};
    colorAttachment.format = m_imageFormat;
    colorAttachment.samples = m_msaaSamples;
    colorAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    colorAttachment.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    colorAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    colorAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    colorAttachment.finalLayout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    /* primitiveID */
    VkAttachmentDescription primitiveIDAttachment{};
    primitiveIDAttachment.format = m_imageFormat; //VK_FORMAT_R8_UINT;
    primitiveIDAttachment.samples = m_msaaSamples;
    primitiveIDAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    primitiveIDAttachment.storeOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    primitiveIDAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    primitiveIDAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    primitiveIDAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    primitiveIDAttachment.finalLayout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    /* depth */
    VkAttachmentDescription depthStencilAttachment{};
    depthStencilAttachment.format = m_depthFormat;
    depthStencilAttachment.samples = m_msaaSamples;
    depthStencilAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    depthStencilAttachment.storeOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    depthStencilAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_CLEAR; //VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    depthStencilAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_STORE; //VK_ATTACHMENT_STORE_OP_DONT_CARE;
    depthStencilAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    depthStencilAttachment.finalLayout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;

    /* multisample resolve */
    VkAttachmentDescription colorAttachmentResolve{};
    colorAttachmentResolve.format = m_imageFormat;
    colorAttachmentResolve.samples = VK_SAMPLE_COUNT_1_BIT;
    colorAttachmentResolve.loadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachmentResolve.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    colorAttachmentResolve.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachmentResolve.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    colorAttachmentResolve.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    colorAttachmentResolve.finalLayout = VK_IMAGE_LAYOUT_PRESENT_SRC_KHR;
    
    VkAttachmentDescription primIDAttachmentResolve{};
    primIDAttachmentResolve.format = m_imageFormat;
    primIDAttachmentResolve.samples = VK_SAMPLE_COUNT_1_BIT;
    primIDAttachmentResolve.loadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    primIDAttachmentResolve.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    primIDAttachmentResolve.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    primIDAttachmentResolve.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    primIDAttachmentResolve.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    primIDAttachmentResolve.finalLayout = VK_IMAGE_LAYOUT_PRESENT_SRC_KHR;

    // /* primitiveID */
    // VkAttachmentDescription primitiveIDAttachment{};
    // primitiveIDAttachment.format = m_imageFormat; //VK_FORMAT_R8_UINT;
    // primitiveIDAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    // primitiveIDAttachment.storeOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    // primitiveIDAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    // primitiveIDAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    // primitiveIDAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    // primitiveIDAttachment.finalLayout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;
    // primitiveIDAttachment.samples = VK_SAMPLE_COUNT_1_BIT;

    // VkAttachmentDescription colorAttachmentResolve2{};
    // colorAttachmentResolve2.format = m_imageFormat;
    // colorAttachmentResolve2.samples = VK_SAMPLE_COUNT_1_BIT;
    // colorAttachmentResolve2.loadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    // colorAttachmentResolve2.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    // colorAttachmentResolve2.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    // colorAttachmentResolve2.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    // colorAttachmentResolve2.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    // colorAttachmentResolve2.finalLayout = VK_IMAGE_LAYOUT_PRESENT_SRC_KHR;

    /* Subpasses and attachment references */
    /* color */
    VkAttachmentReference colorAttachmentRef{};
    colorAttachmentRef.attachment = 0u;
    colorAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    VkAttachmentReference primitiveIDAttachmentRef{};
    primitiveIDAttachmentRef.attachment = 1u;
    primitiveIDAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL; //VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;

    std::vector<VkAttachmentReference> colorAttachmentsRefs;
    colorAttachmentsRefs.push_back(colorAttachmentRef);
    colorAttachmentsRefs.push_back(primitiveIDAttachmentRef);

    /* depth */
    VkAttachmentReference depthStencilAttachmentRef{};
    depthStencilAttachmentRef.attachment = 2u;
    depthStencilAttachmentRef.layout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;

    std::vector<VkAttachmentReference> depthStencilAttachmentRefs;
    depthStencilAttachmentRefs.push_back(depthStencilAttachmentRef);

    /* multisample resolve */
    VkAttachmentReference colorAttachmentResolveRef{};
    colorAttachmentResolveRef.attachment = 3u;
    colorAttachmentResolveRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;
    
    VkAttachmentReference primIDttachmentResolveRef{};
    primIDttachmentResolveRef.attachment = 4u;
    primIDttachmentResolveRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    std::vector<VkAttachmentReference> colorAttachmentResolveRefs;
    colorAttachmentResolveRefs.push_back(colorAttachmentResolveRef);
    colorAttachmentResolveRefs.push_back(primIDttachmentResolveRef);

    // VkAttachmentReference primitiveIDAttachmentRef{};
    // primitiveIDAttachmentRef.attachment = 0u;
    // primitiveIDAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL; //VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
    // colorAttachmentsRefs.push_back(primitiveIDAttachmentRef);
    // VkAttachmentReference depthStencilAttachmentRef2{};
    // depthStencilAttachmentRef2.attachment = 3u;
    // depthStencilAttachmentRef2.layout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;
    // depthStencilAttachmentRefs.push_back(depthStencilAttachmentRef2);
    // VkAttachmentReference colorAttachmentResolveRef2{};
    // colorAttachmentResolveRef2.attachment = VK_ATTACHMENT_UNUSED;
    // colorAttachmentResolveRef2.layout = VK_IMAGE_LAYOUT_UNDEFINED;
    // colorAttachmentResolveRefs.push_back(colorAttachmentResolveRef2);

    // Vulkan may also support compute subpasses in the future, so we have to be explicit about this being a graphics subpass
    VkSubpassDescription subpass{};
    subpass.flags = 0;
    subpass.pipelineBindPoint = m_pipelineBindPoint;
    subpass.colorAttachmentCount = colorAttachmentsRefs.size();
    subpass.pColorAttachments = colorAttachmentsRefs.data();
    subpass.pDepthStencilAttachment = depthStencilAttachmentRefs.data();
    subpass.pResolveAttachments = colorAttachmentResolveRefs.data();
    subpass.preserveAttachmentCount = 0;
    subpass.pPreserveAttachments = NULL;
    subpass.inputAttachmentCount = 0; //1u;
    subpass.pInputAttachments = NULL; //&primitiveIDAttachmentRef;

    // VkSubpassDescription subpass2{};
    // subpass2.flags = 0;
    // subpass2.pipelineBindPoint = m_pipelineBindPoint;
    // subpass2.colorAttachmentCount = colorAttachmentsRefs.size(); //1u;
    // subpass2.pColorAttachments = colorAttachmentsRefs.data(); //&colorAttachmentRef;
    // subpass2.pDepthStencilAttachment = depthStencilAttachmentRefs.data();
    // subpass2.pResolveAttachments = NULL;// colorAttachmentResolveRefs.data();
    // subpass2.preserveAttachmentCount = 0;
    // subpass2.pPreserveAttachments = NULL;
    // subpass2.inputAttachmentCount = 0; //1u;
    // subpass2.pInputAttachments = NULL; //&primitiveIDAttachmentRef;

    std::vector<VkSubpassDescription> subpasses;
    subpasses.push_back(subpass);
    // subpasses.push_back(subpass2);

    // Subpass dependencies
    VkSubpassDependency dependency{};
    dependency.srcSubpass = VK_SUBPASS_EXTERNAL;
    dependency.dstSubpass = 0u;
    dependency.srcStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_LATE_FRAGMENT_TESTS_BIT;
    dependency.srcAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    dependency.dstStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_EARLY_FRAGMENT_TESTS_BIT;
    dependency.dstAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    
    // create Render pass
    // std::array<VkAttachmentDescription,4> attachments = {colorAttachment, primitiveIDAttachment, depthStencilAttachment, colorAttachmentResolve};
    std::array<VkAttachmentDescription, 5> attachments = {colorAttachment, primitiveIDAttachment, depthStencilAttachment, colorAttachmentResolve, primIDAttachmentResolve};
    m_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_CREATE_INFO;
    m_renderPassInfo.pNext = NULL;
    m_renderPassInfo.flags = 0u;
    m_renderPassInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
    m_renderPassInfo.pAttachments = attachments.data();
    m_renderPassInfo.subpassCount = subpasses.size();//1u;
    m_renderPassInfo.pSubpasses = subpasses.data();//&subpass;
    m_renderPassInfo.dependencyCount = 1u;
    m_renderPassInfo.pDependencies = &dependency;

    // create vulkan object
    createvk(vkCreateRenderPass(m_device,
                                &m_renderPassInfo,
                                    nullptr,
                                &m_renderPass));
    return *this;
}
