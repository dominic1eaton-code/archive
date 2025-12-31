/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VFrameBuffer.h"

using namespace ogun;

VFrameBuffer& VFrameBuffer::build(VkRenderPass renderPass)
{
    // the image that we have to use for the attachment depends on which image the swap chain
    // returns when we retrieve one for presentation. That means that we have to create a framebuffer
    // for all of the images in the swap chain and use the one that corresponds to the retrieved
    // image at drawing time.
    // std::array<VkImageView, 2> attachments = {
    //     m_swapChainImageView,
    //     m_depthImageView
    // };

    m_framebufferInfo.sType = VK_STRUCTURE_TYPE_FRAMEBUFFER_CREATE_INFO;
    m_framebufferInfo.pNext = NULL;
    m_framebufferInfo.flags = 0;

    // need to specify with which renderPass the framebuffer needs to be compatible. You can only
    // use a framebuffer with the render passes that it is compatible with, which roughly means that
    // they use the same number and type of attachments.
    m_framebufferInfo.renderPass = renderPass;

    // The attachmentCount and pAttachments parameters specify the VkImageView objects that should
    // be bound to the respective attachment descriptions in the render pass pAttachment array.
    // m_framebufferInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
    // m_framebufferInfo.pAttachments = attachments.data();

    // // The width and height parameters are self-explanatory and layers refers to the number of layers
    // // in image arrays. Our swap chain images are single images, so the number of layers is 1.
    // m_framebufferInfo.width = m_extent.width;
    // m_framebufferInfo.height = m_extent.height;
    m_framebufferInfo.layers = 1u;

    createVk(vkCreateFramebuffer(m_device,
                                &m_framebufferInfo,
                                nullptr,
                                &m_buffer));
    return *this;
}