/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include <iostream>
#include <unordered_map>
#include <map>
#include <string>
#include <queue>
#include <vector>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <chrono>
#include <winsock2.h>
#include <array>
#include <stdexcept>

#define GLM_FORCE_RADIANS
#define GLM_FORCE_DEPTH_ZERO_TO_ONE
#define GLM_ENABLE_EXPERIMENTAL
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtx/hash.hpp>

#include "Hesabu/Window/HWindow.h"
#include "Ogun/Core/VConstants.h"
#include "Ogun/Core/VInstance.h"
#include "Ogun/Core/VDevice.h"
#include "Ogun/Core/VSurface.h"
#include "Ogun/Core/VDescriptorLayout.h"
#include "Ogun/Core/VRenderPass.h"
#include "Ogun/Core/VPipeline.h"
#include "Ogun/Core/VShaderManager.h"
#include "Ogun/Core/VSyncManager.h"
#include "Ogun/Buffer/VFrameBuffer.h"
#include "Ogun/Buffer/VSwapchain.h"
#include "Ogun/Sync/VFence.h"
#include "Ogun/Sync/VSemaphore.h"

#define VK_USE_PLATFORM_WIN32_KHR

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

using namespace ogun;


VkCommandBuffer beginSingleTimeCommands(VkCommandPool commandPool, VkDevice device) 
{
    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandPool = commandPool;
    allocInfo.commandBufferCount = 1;

    VkCommandBuffer commandBuffer;
    vkAllocateCommandBuffers(device, &allocInfo, &commandBuffer);

    VkCommandBufferBeginInfo beginInfo{};
    beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    beginInfo.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;

    vkBeginCommandBuffer(commandBuffer, &beginInfo);

    return commandBuffer;
}

void endSingleTimeCommands(VkCommandBuffer commandBuffer, VkQueue& queue, VkDevice device, VkCommandPool& pool) 
{
    vkEndCommandBuffer(commandBuffer);

    VkSubmitInfo submitInfo{};
    submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    submitInfo.commandBufferCount = 1;
    submitInfo.pCommandBuffers = &commandBuffer;

    VkResult result = vkQueueSubmit(queue, 1, &submitInfo, VK_NULL_HANDLE);
    vkQueueWaitIdle(queue);

    vkFreeCommandBuffers(device, pool, 1, &commandBuffer);
}

void copyBuffer(VkBuffer srcBuffer, VkBuffer dstBuffer, VkDeviceSize size, VkQueue& queue, VkDevice device, VkCommandPool& pool) 
{
    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    VkBufferCopy copyRegion{};
    copyRegion.size = size;
    vkCmdCopyBuffer(commandBuffer, srcBuffer, dstBuffer, 1, &copyRegion);
    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

VkCommandPool createCommandPool(VkDevice device, std::optional<uint32_t> index)
{
    VObject<int> obj;
    VkCommandPool commandPool;
    VkCommandPoolCreateInfo poolInfo{};
    poolInfo.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
    poolInfo.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
    poolInfo.queueFamilyIndex = index.value();

    obj.createvk(vkCreateCommandPool(device,
                                     &poolInfo,
                                     nullptr,
                                     &commandPool));
    return commandPool;
}

std::vector<VkCommandBuffer> createCommandBuffers(VkDevice device, VkCommandPool pool) 
{
    std::vector<VkCommandBuffer> commandBuffers;
    VObject<int> obj;
    commandBuffers.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);

    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.commandPool = pool;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandBufferCount = (uint32_t) commandBuffers.size();

    obj.createvk(vkAllocateCommandBuffers(device,
                                     &allocInfo,
                                     commandBuffers.data()));
    return commandBuffers;    
}

uint32_t findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties, VkPhysicalDeviceMemoryProperties memProperties)
{
    for (uint32_t i = 0; i < memProperties.memoryTypeCount; i++) 
    {
        if ((typeFilter & (1 << i)) && (memProperties.memoryTypes[i].propertyFlags & properties) == properties) 
        {
            return i;
        }
    }
    throw std::runtime_error("failed to find suitable memory type!");
}

void createImage(VkDevice device, uint32_t width, uint32_t height, uint32_t mipLevels, VkSampleCountFlagBits numSamples, VkFormat format, VkImageTiling tiling, VkImageUsageFlags usage, VkMemoryPropertyFlags properties, VkImage& image, VkDeviceMemory& imageMemory, VkPhysicalDeviceMemoryProperties memProperties)
{
    VObject<int> obj;
    VkImageCreateInfo imageInfo{};
    imageInfo.sType = VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO;
    imageInfo.imageType = VK_IMAGE_TYPE_2D;
    imageInfo.extent.width = width;
    imageInfo.extent.height = height;
    imageInfo.extent.depth = 1;
    imageInfo.mipLevels = mipLevels;
    imageInfo.arrayLayers = 1;
    imageInfo.format = format;
    imageInfo.tiling = tiling;
    imageInfo.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    imageInfo.usage = usage;
    imageInfo.samples = numSamples;
    imageInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    obj.createvk(vkCreateImage(device,
                                &imageInfo,
                                nullptr,
                                &image));

    VkMemoryRequirements memRequirements;
    vkGetImageMemoryRequirements(device, image, &memRequirements);

    VkMemoryAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    allocInfo.allocationSize = memRequirements.size;
    allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, properties, memProperties);

    obj.createvk(vkAllocateMemory(device,
                                &allocInfo,
                                nullptr,
                                &imageMemory));

    vkBindImageMemory(device, image, imageMemory, 0);
}

VkImageView createImageView(VkDevice device, VkImage image, VkFormat format, VkImageAspectFlags aspectFlags, uint32_t mipLevels) 
{
    VObject<int> obj;
    VkImageViewCreateInfo viewInfo{};
    viewInfo.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
    viewInfo.image = image;
    viewInfo.viewType = VK_IMAGE_VIEW_TYPE_2D;
    viewInfo.format = format;
    viewInfo.subresourceRange.aspectMask = aspectFlags;
    viewInfo.subresourceRange.baseMipLevel = 0;
    viewInfo.subresourceRange.levelCount = mipLevels;
    viewInfo.subresourceRange.baseArrayLayer = 0;
    viewInfo.subresourceRange.layerCount = 1;

    VkImageView imageView;
    
    obj.createvk(vkCreateImageView(device,
                                &viewInfo,
                                nullptr,
                                &imageView));
    return imageView;
}


VkFormat findSupportedFormat(VkPhysicalDevice pdevice, const std::vector<VkFormat>& candidates, VkImageTiling tiling, VkFormatFeatureFlags features) 
{
    for (VkFormat format : candidates) {
        VkFormatProperties props;
        vkGetPhysicalDeviceFormatProperties(pdevice, format, &props);

        if (tiling == VK_IMAGE_TILING_LINEAR && (props.linearTilingFeatures & features) == features) {
            return format;
        } else if (tiling == VK_IMAGE_TILING_OPTIMAL && (props.optimalTilingFeatures & features) == features) {
            return format;
        }
    }

    throw std::runtime_error("failed to find supported format!");
}

VkFormat findDepthFormat(VkPhysicalDevice pdevice) 
{
    return findSupportedFormat(pdevice,
        {VK_FORMAT_D32_SFLOAT, VK_FORMAT_D32_SFLOAT_S8_UINT, VK_FORMAT_D24_UNORM_S8_UINT},
        VK_IMAGE_TILING_OPTIMAL,
        VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT
    );
}

void createColorResources(VkDevice device, VkFormat colorFormat, VkSampleCountFlagBits msaaSamples, VkImage& colorImage, VkDeviceMemory& colorImageMemory, 
                          VkExtent2D extent,  VkPhysicalDeviceMemoryProperties memProperties, uint32_t mipLevels, VkImageView& imageView) 
{
    createImage(device, extent.width, extent.height, 1, msaaSamples, colorFormat, VK_IMAGE_TILING_OPTIMAL, 
                VK_IMAGE_USAGE_TRANSIENT_ATTACHMENT_BIT | VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, 
                colorImage, colorImageMemory, memProperties);
    imageView = createImageView(device, colorImage, colorFormat, VK_IMAGE_ASPECT_COLOR_BIT, mipLevels);
}

void createDepthResources(VkDevice device, VkPhysicalDevice pdevice, VkSampleCountFlagBits msaaSamples, VkImage& depthImage,
                          VkDeviceMemory& depthImageMemory, VkExtent2D extent, VkPhysicalDeviceMemoryProperties memProperties, uint32_t mipLevels,
                          VkImageView& imageView) 
{
    VkFormat depthFormat = findDepthFormat(pdevice);

    createImage(device, extent.width, extent.height, 1, msaaSamples, depthFormat, VK_IMAGE_TILING_OPTIMAL, 
                VK_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, depthImage, 
                depthImageMemory, memProperties);
    imageView = createImageView(device, depthImage, depthFormat, VK_IMAGE_ASPECT_DEPTH_BIT, mipLevels);
}

void createFramebuffers(VkDevice device, VkExtent2D extent, VkRenderPass renderpass, VkImageView colorImageView, VkImageView depthImageView, std::vector<VkImageView> imageViews, std::vector<VkFramebuffer>& frameBuffers)
{
    VObject<int> obj;
    frameBuffers.resize(imageViews.size());
    for (size_t i = 0; i < imageViews.size(); i++)
    {
        std::array<VkImageView, 3> attachments = {
            colorImageView,
            depthImageView,
            imageViews[i]
        };

        VkFramebufferCreateInfo framebufferInfo{};
        framebufferInfo.sType = VK_STRUCTURE_TYPE_FRAMEBUFFER_CREATE_INFO;
        framebufferInfo.renderPass = renderpass;
        framebufferInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
        framebufferInfo.pAttachments = attachments.data();
        framebufferInfo.width = extent.width;
        framebufferInfo.height = extent.height;
        framebufferInfo.layers = 1;
        obj.createvk(vkCreateFramebuffer(device,
                                    &framebufferInfo,
                                    nullptr,
                                    &frameBuffers[i]));
    }
}

void copyBufferToImage(VkBuffer buffer, VkImage image, uint32_t width, uint32_t height, VkQueue& queue, VkCommandPool& pool, VkDevice device)
{
    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    VkBufferImageCopy region{};
    region.bufferOffset = 0;
    region.bufferRowLength = 0;
    region.bufferImageHeight = 0;
    region.imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    region.imageSubresource.mipLevel = 0;
    region.imageSubresource.baseArrayLayer = 0;
    region.imageSubresource.layerCount = 1;
    region.imageOffset = {0, 0, 0};
    region.imageExtent = {
        width,
        height,
        1
    };
    vkCmdCopyBufferToImage(commandBuffer, buffer, image, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, 1, &region);
    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

void transitionImageLayout(VkImage image, VkFormat format, VkImageLayout oldLayout, VkImageLayout newLayout, uint32_t mipLevels, VkQueue& queue, VkCommandPool& pool, VkDevice device) 
{
    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    VkImageMemoryBarrier barrier{};
    barrier.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
    barrier.oldLayout = oldLayout;
    barrier.newLayout = newLayout;
    barrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.image = image;
    barrier.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    barrier.subresourceRange.baseMipLevel = 0;
    barrier.subresourceRange.levelCount = mipLevels;
    barrier.subresourceRange.baseArrayLayer = 0;
    barrier.subresourceRange.layerCount = 1;

    VkPipelineStageFlags sourceStage;
    VkPipelineStageFlags destinationStage;

    if (oldLayout == VK_IMAGE_LAYOUT_UNDEFINED && newLayout == VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL) 
    {
        barrier.srcAccessMask = 0;
        barrier.dstAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;

        sourceStage = VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT;
        destinationStage = VK_PIPELINE_STAGE_TRANSFER_BIT;
    } 
    else if (oldLayout == VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL && newLayout == VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL) 
    {
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

        sourceStage = VK_PIPELINE_STAGE_TRANSFER_BIT;
        destinationStage = VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT;
    } 
    else 
    {
        throw std::invalid_argument("unsupported layout transition!");
    }

    vkCmdPipelineBarrier(
        commandBuffer,
        sourceStage, destinationStage,
        0,
        0, nullptr,
        0, nullptr,
        1, &barrier
    );

    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

void generateMipmaps(VkFormatProperties formatProperties, VkImage image, VkFormat imageFormat, int32_t texWidth, int32_t texHeight, uint32_t mipLevels, VkQueue& queue, VkCommandPool& pool, VkDevice device) 
{
    // Check if image format supports linear imageFormat
    if (!(formatProperties.optimalTilingFeatures & VK_FORMAT_FEATURE_SAMPLED_IMAGE_FILTER_LINEAR_BIT)) {
        throw std::runtime_error("texture image format does not support linear blitting!");
    }

    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);

    VkImageMemoryBarrier barrier{};
    barrier.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
    barrier.image = image;
    barrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    barrier.subresourceRange.baseArrayLayer = 0;
    barrier.subresourceRange.layerCount = 1;
    barrier.subresourceRange.levelCount = 1;

    int32_t mipWidth = texWidth;
    int32_t mipHeight = texHeight;

    for (uint32_t i = 1; i < mipLevels; i++) 
    {
        barrier.subresourceRange.baseMipLevel = i - 1;
        barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
        barrier.newLayout = VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL;
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        barrier.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;

        vkCmdPipelineBarrier(commandBuffer,
            VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT, 0,
            0, nullptr,
            0, nullptr,
            1, &barrier);

        VkImageBlit blit{};
        blit.srcOffsets[0] = {0, 0, 0};
        blit.srcOffsets[1] = {mipWidth, mipHeight, 1};
        blit.srcSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        blit.srcSubresource.mipLevel = i - 1;
        blit.srcSubresource.baseArrayLayer = 0;
        blit.srcSubresource.layerCount = 1;
        blit.dstOffsets[0] = {0, 0, 0};
        blit.dstOffsets[1] = { mipWidth > 1 ? mipWidth / 2 : 1, mipHeight > 1 ? mipHeight / 2 : 1, 1 };
        blit.dstSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        blit.dstSubresource.mipLevel = i;
        blit.dstSubresource.baseArrayLayer = 0;
        blit.dstSubresource.layerCount = 1;

        vkCmdBlitImage(commandBuffer,
            image, VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL,
            image, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL,
            1, &blit,
            VK_FILTER_LINEAR);

        barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL;
        barrier.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
        barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

        vkCmdPipelineBarrier(commandBuffer,
            VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT, 0,
            0, nullptr,
            0, nullptr,
            1, &barrier);

        if (mipWidth > 1) mipWidth /= 2;
        if (mipHeight > 1) mipHeight /= 2;
    }

    barrier.subresourceRange.baseMipLevel = mipLevels - 1;
    barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
    barrier.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
    barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
    barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

    vkCmdPipelineBarrier(commandBuffer,
        VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT, 0,
        0, nullptr,
        0, nullptr,
        1, &barrier);

    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

void createBuffer(VkDevice device, VkDeviceSize size, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties, VkBuffer& buffer, VkDeviceMemory& bufferMemory, VkPhysicalDeviceMemoryProperties memProperties) 
{
    VkBufferCreateInfo bufferInfo{};
    bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    bufferInfo.size = size;
    bufferInfo.usage = usage;
    bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    if (vkCreateBuffer(device, &bufferInfo, nullptr, &buffer) != VK_SUCCESS) {
        throw std::runtime_error("failed to create buffer!");
    }

    VkMemoryRequirements memRequirements;
    vkGetBufferMemoryRequirements(device, buffer, &memRequirements);

    VkMemoryAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    allocInfo.allocationSize = memRequirements.size;
    allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, properties, memProperties);

    if (vkAllocateMemory(device, &allocInfo, nullptr, &bufferMemory) != VK_SUCCESS) {
        throw std::runtime_error("failed to allocate buffer memory!");
    }

    vkBindBufferMemory(device, buffer, bufferMemory, 0);
}

void createTextureImage(VkPhysicalDevice pdevice, VkDevice device, std::string texture, VkQueue& queue, VkCommandPool& pool, 
                        VkPhysicalDeviceMemoryProperties memProperties, VkImage& textureImage, VkDeviceMemory& textureImageMemory, uint32_t& mipLevels)
{
    int texWidth, texHeight, texChannels;
    // loadTexture();
    stbi_uc* pixels = stbi_load(texture.c_str(), &texWidth, &texHeight, &texChannels, STBI_rgb_alpha);
    VkDeviceSize imageSize = texWidth * texHeight * 4;
    mipLevels = static_cast<uint32_t>(std::floor(std::log2(std::max(texWidth, texHeight)))) + 1;
    if (!pixels)
    {
        throw std::runtime_error("failed to load texture image!");
    }
    VkBuffer stagingBuffer;
    VkDeviceMemory stagingBufferMemory;
    createBuffer(device, imageSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
    void* data;
    vkMapMemory(device, stagingBufferMemory, 0, imageSize, 0, &data);
        memcpy(data, pixels, static_cast<size_t>(imageSize));
    vkUnmapMemory(device, stagingBufferMemory);
    stbi_image_free(pixels);
    createImage(device, texWidth, texHeight, mipLevels, VK_SAMPLE_COUNT_1_BIT, VK_FORMAT_R8G8B8A8_SRGB, VK_IMAGE_TILING_OPTIMAL, VK_IMAGE_USAGE_TRANSFER_SRC_BIT | VK_IMAGE_USAGE_TRANSFER_DST_BIT | VK_IMAGE_USAGE_SAMPLED_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, textureImage, textureImageMemory, memProperties);
    transitionImageLayout(textureImage, VK_FORMAT_R8G8B8A8_SRGB, VK_IMAGE_LAYOUT_UNDEFINED, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, mipLevels, queue, pool, device);
    copyBufferToImage(stagingBuffer, textureImage, static_cast<uint32_t>(texWidth), static_cast<uint32_t>(texHeight), queue, pool, device);
    //transitioned to VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL while generating mipmaps
    vkDestroyBuffer(device, stagingBuffer, nullptr);
    vkFreeMemory(device, stagingBufferMemory, nullptr);
    VkFormatProperties formatProperties;
    VkFormat imageFormat = VK_FORMAT_R8G8B8A8_SRGB;
    vkGetPhysicalDeviceFormatProperties(pdevice, imageFormat, &formatProperties);
    generateMipmaps(formatProperties, textureImage, VK_FORMAT_R8G8B8A8_SRGB, texWidth, texHeight, mipLevels, queue, pool, device);
}

void createTextureImageView(VkDevice device, VkImage textureImage, uint32_t mipLevels, VkImageView& textureImageView, VkFormat format = VK_FORMAT_R8G8B8A8_SRGB, VkImageAspectFlagBits aspectFlags = VK_IMAGE_ASPECT_COLOR_BIT)
{
    textureImageView = createImageView(device, textureImage, format, aspectFlags, mipLevels);
}

void createTextureSampler(VkPhysicalDeviceProperties properties, VkDevice device, VkSampler& textureSampler)
{
    VObject<int> obj;
    VkSamplerCreateInfo samplerInfo{};
    samplerInfo.sType = VK_STRUCTURE_TYPE_SAMPLER_CREATE_INFO;
    samplerInfo.magFilter = VK_FILTER_LINEAR;
    samplerInfo.minFilter = VK_FILTER_LINEAR;
    samplerInfo.addressModeU = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    samplerInfo.addressModeV = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    samplerInfo.addressModeW = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    samplerInfo.anisotropyEnable = VK_TRUE;
    samplerInfo.maxAnisotropy = properties.limits.maxSamplerAnisotropy;
    samplerInfo.borderColor = VK_BORDER_COLOR_INT_OPAQUE_BLACK;
    samplerInfo.unnormalizedCoordinates = VK_FALSE;
    samplerInfo.compareEnable = VK_FALSE;
    samplerInfo.compareOp = VK_COMPARE_OP_ALWAYS;
    samplerInfo.mipmapMode = VK_SAMPLER_MIPMAP_MODE_LINEAR;
    samplerInfo.minLod = 0.0f;
    samplerInfo.maxLod = VK_LOD_CLAMP_NONE;
    samplerInfo.mipLodBias = 0.0f;
    obj.createvk(vkCreateSampler(device,
                                &samplerInfo,
                                nullptr,
                                &textureSampler));
}

// // void loadModel()
// // {
// // }

void createCommandBuffers(VkDevice device, VkCommandPool& pool,  std::vector<VkCommandBuffer>& commandBuffers) 
{
    commandBuffers.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.commandPool = pool;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandBufferCount = (uint32_t) commandBuffers.size();

    if (vkAllocateCommandBuffers(device, &allocInfo, commandBuffers.data()) != VK_SUCCESS) {
        throw std::runtime_error("failed to allocate command buffers!");
    }
}

void createSyncObjects(std::vector<VkSemaphore>& imageAvailableSemaphores, std::vector<VkSemaphore>& renderFinishedSemaphores, std::vector<VkFence>& inFlightFences, VkDevice device)
{
    imageAvailableSemaphores.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
    renderFinishedSemaphores.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
    inFlightFences.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);

    VkSemaphoreCreateInfo semaphoreInfo{};
    semaphoreInfo.sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO;

    VkFenceCreateInfo fenceInfo{};
    fenceInfo.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
    fenceInfo.flags = VK_FENCE_CREATE_SIGNALED_BIT;

    for (size_t i = 0; i < ogun::constants::MAX_FRAMES_IN_FLIGHT; i++) {
        if (vkCreateSemaphore(device, &semaphoreInfo, nullptr, &imageAvailableSemaphores[i]) != VK_SUCCESS ||
            vkCreateSemaphore(device, &semaphoreInfo, nullptr, &renderFinishedSemaphores[i]) != VK_SUCCESS ||
            vkCreateFence(device, &fenceInfo, nullptr, &inFlightFences[i]) != VK_SUCCESS) {
            throw std::runtime_error("failed to create synchronization objects for a frame!");
        }
    }
}

void recordCommandBuffer(VkCommandBuffer& commandBuffer, uint32_t imageIndex, VkRenderPass renderpass, VkExtent2D extent, VkFramebuffer framebuffer,
                         VkPipeline pipeline, std::vector<VkBuffer> vertexBuffers, VkBuffer indexBuffer, VkPipelineLayout layout, std::vector<VkDescriptorSet> descriptorsets,
                         uint32_t indicesCount)
{
    VkCommandBufferBeginInfo beginInfo{};
    beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;

    if (vkBeginCommandBuffer(commandBuffer, &beginInfo) != VK_SUCCESS) {
        throw std::runtime_error("failed to begin recording command buffer!");
    }

    VkRenderPassBeginInfo renderPassInfo{};
    renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;
    renderPassInfo.renderPass = renderpass;
    renderPassInfo.framebuffer = framebuffer;
    renderPassInfo.renderArea.offset = {0, 0};
    renderPassInfo.renderArea.extent = extent;

    std::array<VkClearValue, 2> clearValues{};
    clearValues[0].color = {{0.0f, 0.0f, 0.0f, 1.0f}};
    clearValues[1].depthStencil = {1.0f, 1.0F};

    renderPassInfo.clearValueCount = static_cast<uint32_t>(clearValues.size());
    renderPassInfo.pClearValues = clearValues.data();

    vkCmdBeginRenderPass(commandBuffer, &renderPassInfo, VK_SUBPASS_CONTENTS_INLINE);

        vkCmdBindPipeline(commandBuffer, VK_PIPELINE_BIND_POINT_GRAPHICS, pipeline);

        VkViewport viewport{};
        viewport.x = 0.0f;
        viewport.y = 0.0f;
        viewport.width = (float) extent.width;
        viewport.height = (float) extent.height;
        viewport.minDepth = 0.0f;
        viewport.maxDepth = 1.0f;
        vkCmdSetViewport(commandBuffer, 0, 1, &viewport);

        VkRect2D scissor{};
        scissor.offset = {0, 0};
        scissor.extent = extent;
        vkCmdSetScissor(commandBuffer, 0, 1, &scissor);

        VkDeviceSize offsets[] = {0};
        vkCmdBindVertexBuffers(commandBuffer, 0, vertexBuffers.size(), vertexBuffers.data(), offsets);

        vkCmdBindIndexBuffer(commandBuffer, indexBuffer, 0, VK_INDEX_TYPE_UINT32);

        vkCmdBindDescriptorSets(commandBuffer, VK_PIPELINE_BIND_POINT_GRAPHICS, layout, 0, descriptorsets.size(), descriptorsets.data(), 0, nullptr);

        vkCmdDrawIndexed(commandBuffer, static_cast<uint32_t>(indicesCount), 1, 0, 0, 0);

    vkCmdEndRenderPass(commandBuffer);

    if (vkEndCommandBuffer(commandBuffer) != VK_SUCCESS)
    {
        throw std::runtime_error("failed to record command buffer!");
    }
}






void VulkanModel::draw(float tick)
{
    std::vector<VkFence> inFlightFences = m_fences->find("inflight")->set();
    std::vector<VkSemaphore> imageAvailableSemaphores = m_semaphores->find("imageAvailable")->set();
    std::vector<VkSemaphore> renderFinishedSemaphores = m_semaphores->find("renderFinished")->set();
    vkWaitForFences(m_device, 1, &inFlightFences[m_frameIndex], VK_TRUE, UINT64_MAX);

    uint32_t imageIndex;
    VkResult result = vkAcquireNextImageKHR(m_device, m_swapchain.chain(), UINT64_MAX, imageAvailableSemaphores[m_frameIndex], VK_NULL_HANDLE, &imageIndex);

    if (result == VK_ERROR_OUT_OF_DATE_KHR) 
    {
        m_swapchain.rebuild();
        return;
    } 
    else if (result != VK_SUCCESS && result != VK_SUBOPTIMAL_KHR) 
    {
        throw std::runtime_error("failed to acquire swap chain image!");
    }

    VkExtent2D extent = m_swapchain.extent();
    std::vector<void*> uniformBuffersMapped;
    m_shader->update(tick, m_frameIndex);

    vkResetFences(m_device, 1, &inFlightFences[m_frameIndex]);
    vkResetCommandBuffer(m_commandBuffers[m_frameIndex], 0);

    
    /*****************************************************************************************************/
    // m_indexBuffer = m_shader->indexBuffer();
    // m_vertexBuffers = m_shader->vertexBuffers();
    std::vector<VkDescriptorSet> descriptorSets;
    descriptorSets.push_back(m_shader->descriptorSets()[m_frameIndex]);
    recordCommandBuffer(m_commandBuffers[m_frameIndex], imageIndex, m_renderpass, extent, m_framebuffers[m_frameIndex], m_pipelines[0], 
                        m_shader->vertexBuffers(),  m_shader->indexBuffer(), m_layout, descriptorSets, m_indicesCount, m_vertsCount,
                        m_device, m_vertices, m_indices, m_queues[0], m_commandPool, m_memProperties);
    descriptorSets.clear();
    // VkBuffer vertexBuffer;
    // VkDeviceMemory vertexBufferMemory;
    // VkDeviceSize bufferSize = sizeof(m_vertices[0]) * m_vertices.size();

    // VkBuffer stagingBuffer;
    // VkDeviceMemory stagingBufferMemory;

    // //******** createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
    // VkBufferCreateInfo bufferInfo{};
    // bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    // bufferInfo.size = bufferSize;
    // bufferInfo.usage = VK_BUFFER_USAGE_TRANSFER_SRC_BIT;
    // bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
    // if (vkCreateBuffer(m_device, &bufferInfo, nullptr, &stagingBuffer) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to create buffer!");
    // }
    // VkMemoryRequirements memRequirements;
    // vkGetBufferMemoryRequirements(m_device, stagingBuffer, &memRequirements);
    // VkMemoryAllocateInfo allocInfo{};
    // allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    // allocInfo.allocationSize = memRequirements.size;
    // allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, m_memProperties);
    // if (vkAllocateMemory(m_device, &allocInfo, nullptr, &stagingBufferMemory) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to allocate buffer memory!");
    // }
    // vkBindBufferMemory(m_device, stagingBuffer, stagingBufferMemory, 0);

    // //******** createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
    // VkBufferCreateInfo bufferInfo{};
    // bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    // bufferInfo.size = bufferSize;
    // bufferInfo.usage = VK_BUFFER_USAGE_VERTEX_BUFFER_BIT;
    // bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    // if (vkCreateBuffer(m_device, &bufferInfo, nullptr, &vertexBuffer) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to create buffer!");
    // }

    // VkMemoryRequirements memRequirements;
    // vkGetBufferMemoryRequirements(m_device, vertexBuffer, &memRequirements);

    // VkMemoryAllocateInfo allocInfo{};
    // allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    // allocInfo.allocationSize = memRequirements.size;
    // allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, m_memProperties);

    // if (vkAllocateMemory(m_device, &allocInfo, nullptr, &vertexBufferMemory) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to allocate buffer memory!");
    // }

    // vkBindBufferMemory(m_device, vertexBuffer, vertexBufferMemory, 0);


    // void* data;
    // vkMapMemory(m_device, vertexBufferMemory, 0, bufferSize, 0, &data);
    //     memcpy(data, m_vertices.data(), (size_t) bufferSize);
    // vkUnmapMemory(m_device, vertexBufferMemory);


    // //******** createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, vertexBuffer, vertexBufferMemory, memProperties);
    // VkBufferCreateInfo dbufferInfo{};
    // dbufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    // dbufferInfo.size = bufferSize;
    // dbufferInfo.usage = VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT;
    // dbufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    // if (vkCreateBuffer(m_device, &dbufferInfo, nullptr, &vertexBuffer) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to create buffer!");
    // }

    // VkMemoryRequirements tmemRequirements;
    // vkGetBufferMemoryRequirements(m_device, vertexBuffer, &tmemRequirements);

    // VkMemoryAllocateInfo tallocInfo{};
    // tallocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    // tallocInfo.allocationSize = tmemRequirements.size;
    // tallocInfo.memoryTypeIndex = findMemoryType(tmemRequirements.memoryTypeBits, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, m_memProperties);

    // if (vkAllocateMemory(m_device, &tallocInfo, nullptr, &vertexBufferMemory) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to allocate buffer memory!");
    // }

    // vkBindBufferMemory(m_device, vertexBuffer, vertexBufferMemory, 0);


    //  //******** copyBuffer(stagingBuffer, vertexBuffer, bufferSize, queue, device, pool);
    // //******** VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    // VkCommandBuffer zcommandBuffer;

    // VkCommandBufferAllocateInfo zallocInfo{};
    // zallocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    // zallocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    // zallocInfo.commandPool = m_commandPool;
    // zallocInfo.commandBufferCount = 1;

    // // VkCommandBuffer commandBuffer;
    // vkAllocateCommandBuffers(m_device, &zallocInfo, &zcommandBuffer);

    // VkCommandBufferBeginInfo beginInfo{};
    // beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    // beginInfo.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;

    // vkBeginCommandBuffer(zcommandBuffer, &beginInfo);

    // // return commandBuffer;

    // VkBufferCopy copyRegion{};
    // copyRegion.srcOffset = 0; // Optional
    // copyRegion.dstOffset = 0; // Optional
    // copyRegion.size = bufferSize;
    // vkCmdCopyBuffer(zcommandBuffer,stagingBuffer, vertexBuffer, 1, &copyRegion);

    // //******** endSingleTimeCommands(commandBuffer, queue, device, commandPool);
    // vkEndCommandBuffer(zcommandBuffer);
    // VkSubmitInfo submitInfo{};
    // submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    // submitInfo.commandBufferCount = 1;
    // submitInfo.pCommandBuffers = &zcommandBuffer;
    // /* VkResult result = */ vkQueueSubmit(m_queues[0], 1, &submitInfo, VK_NULL_HANDLE);
    // vkQueueWaitIdle(m_queues[0]);
    // vkFreeCommandBuffers(m_device, m_commandPool, 1, &zcommandBuffer);


    // vkDestroyBuffer(m_device, stagingBuffer, nullptr);
    // vkFreeMemory(m_device, stagingBufferMemory, nullptr);
    // std::vector<VkBuffer> m_vertexBuffers;
    // m_vertexBuffers.push_back(vertexBuffer);


    // /*****************************************************************************************************/
    // /*****************************************************************************************************/
    // VkCommandBuffer commandBuffer = m_commandBuffers[m_frameIndex];
    // VkCommandBufferBeginInfo zbeginInfo{};
    // zbeginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;

    // if (vkBeginCommandBuffer(commandBuffer, &zbeginInfo) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to begin recording command buffer!");
    // }

    // VkRenderPassBeginInfo renderPassInfo{};
    // renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;
    // renderPassInfo.renderPass = m_renderpass;
    // renderPassInfo.framebuffer = m_framebuffers[m_frameIndex];
    // renderPassInfo.renderArea.offset = {0, 0};
    // renderPassInfo.renderArea.extent = extent;

    // std::array<VkClearValue, 2> clearValues{};
    // clearValues[0].color = {{0.0f, 0.0f, 0.0f, 1.0f}};
    // clearValues[1].depthStencil = {1.0f, 0};

    // renderPassInfo.clearValueCount = static_cast<uint32_t>(clearValues.size());
    // renderPassInfo.pClearValues = clearValues.data();

    // vkCmdBeginRenderPass(commandBuffer, &renderPassInfo, VK_SUBPASS_CONTENTS_INLINE);

    //     vkCmdBindPipeline(commandBuffer, VK_PIPELINE_BIND_POINT_GRAPHICS, m_pipelines[0]);

    //     VkViewport viewport{};
    //     viewport.x = 0.0f;
    //     viewport.y = 0.0f;
    //     viewport.width = (float) extent.width;
    //     viewport.height = (float) extent.height;
    //     viewport.minDepth = 0.0f;
    //     viewport.maxDepth = 1.0f;
    //     vkCmdSetViewport(commandBuffer, 0, 1, &viewport);

    //     VkRect2D scissor{};
    //     scissor.offset = {0, 0};
    //     scissor.extent = extent;
    //     vkCmdSetScissor(commandBuffer, 0, 1, &scissor);

    //     VkDeviceSize offsets[] = {0};
    //     VkBuffer vertexBuffers[] = {vertexBuffer};
    //     vkCmdBindVertexBuffers(commandBuffer, 0, 1, vertexBuffers, offsets);

    //     vkCmdBindIndexBuffer(commandBuffer, indexBuffer, 0, VK_INDEX_TYPE_UINT16);

    //     vkCmdBindDescriptorSets(commandBuffer, VK_PIPELINE_BIND_POINT_GRAPHICS, layout, 0, descriptorsets.size(), descriptorsets.data(), 0, nullptr);

    //     vkCmdDrawIndexed(commandBuffer, static_cast<uint32_t>(indicesCount), 1, 0, 0, 0);
        
    //     // vkCmdDraw(commandBuffer, static_cast<uint32_t>(m_vertices.size()), 1, 0, 0);

    // vkCmdEndRenderPass(commandBuffer);

    // if (vkEndCommandBuffer(commandBuffer) != VK_SUCCESS)
    // {
    //     throw std::runtime_error("failed to record command buffer!");
    // }

    // /*****************************************************************************************************/

    std::vector<VkSemaphore> waitSemaphores;
    waitSemaphores.push_back(imageAvailableSemaphores[m_frameIndex]);
    VkPipelineStageFlags waitStages[] = {VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT};
    
    std::vector<VkSemaphore> signalSemaphores;
    signalSemaphores.push_back(renderFinishedSemaphores[m_frameIndex]);
    
    std::vector<VkSwapchainKHR> swapChains;
    swapChains.push_back(m_swapchain.chain());

    std::vector<VkCommandBuffer> submitBuffers;
    submitBuffers.push_back(m_commandBuffers[m_frameIndex]);

    VkSubmitInfo csubmitInfo{};
    csubmitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    csubmitInfo.pNext = NULL;
    csubmitInfo.waitSemaphoreCount = waitSemaphores.size();
    csubmitInfo.pWaitSemaphores = waitSemaphores.data();
    csubmitInfo.pWaitDstStageMask = waitStages;
    csubmitInfo.commandBufferCount = submitBuffers.size();
    csubmitInfo.pCommandBuffers = submitBuffers.data();
    csubmitInfo.signalSemaphoreCount = signalSemaphores.size();
    csubmitInfo.pSignalSemaphores = signalSemaphores.data();
    if (vkQueueSubmit(m_queues[0], 1, &csubmitInfo, inFlightFences[m_frameIndex]) != VK_SUCCESS)
    {
        throw std::runtime_error("failed to submit draw command buffer!");
    }

    VkPresentInfoKHR presentInfo{};
    presentInfo.sType = VK_STRUCTURE_TYPE_PRESENT_INFO_KHR;
    presentInfo.pNext = NULL;
    presentInfo.waitSemaphoreCount = waitSemaphores.size();
    presentInfo.pWaitSemaphores = signalSemaphores.data();
    presentInfo.swapchainCount = swapChains.size();
    presentInfo.pSwapchains = swapChains.data();
    presentInfo.pImageIndices = &imageIndex;
    result = vkQueuePresentKHR(m_queues[0], &presentInfo);

    bool framebufferResized = false;
    if (result == VK_ERROR_OUT_OF_DATE_KHR || result == VK_SUBOPTIMAL_KHR || framebufferResized)
    {
        framebufferResized = false;
        m_swapchain.rebuild();
    }
    else if (result != VK_SUCCESS)
    {
        throw std::runtime_error("failed to present swap chain image!");
    }

    m_frameIndex = (m_frameIndex + 1) % ogun::constants::MAX_FRAMES_IN_FLIGHT;
}








/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "vulkan_model.h"

using namespace ogun;

VkCommandBuffer VulkanModel::beginSingleTimeCommands(VkCommandPool commandPool, VkDevice device)
{
    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandPool = commandPool;
    allocInfo.commandBufferCount = 1;

    VkCommandBuffer commandBuffer;
    vkAllocateCommandBuffers(device, &allocInfo, &commandBuffer);

    VkCommandBufferBeginInfo beginInfo{};
    beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    beginInfo.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;

    vkBeginCommandBuffer(commandBuffer, &beginInfo);

    return commandBuffer;
}

void VulkanModel::endSingleTimeCommands(VkCommandBuffer& commandBuffer, VkQueue& queue, VkDevice device, VkCommandPool& pool) 
{
    vkEndCommandBuffer(commandBuffer);

    VkSubmitInfo submitInfo{};
    submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    submitInfo.commandBufferCount = 1;
    submitInfo.pCommandBuffers = &commandBuffer;

    VkResult result = vkQueueSubmit(queue, 1, &submitInfo, VK_NULL_HANDLE);
    vkQueueWaitIdle(queue);

    vkFreeCommandBuffers(device, pool, 1, &commandBuffer);
}

void VulkanModel::copyBuffer(VkBuffer srcBuffer, VkBuffer dstBuffer, VkDeviceSize size, VkQueue& queue, VkDevice device, VkCommandPool& pool)
{
    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    VkBufferCopy copyRegion{};
    copyRegion.srcOffset = 0; // Optional
    copyRegion.dstOffset = 0; // Optional
    copyRegion.size = size;
    vkCmdCopyBuffer(commandBuffer, srcBuffer, dstBuffer, 1, &copyRegion);
    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

VkCommandPool VulkanModel::createCommandPool(VkDevice device, std::optional<uint32_t> index)
{
    VObject<int> obj;
    VkCommandPool commandPool;
    VkCommandPoolCreateInfo poolInfo{};
    poolInfo.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
    poolInfo.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
    poolInfo.queueFamilyIndex = index.value();

    obj.createvk(vkCreateCommandPool(device,
                                     &poolInfo,
                                     nullptr,
                                     &commandPool));
    return commandPool;
}

std::vector<VkCommandBuffer> VulkanModel::createCommandBuffers(VkDevice device, VkCommandPool pool) 
{
    std::vector<VkCommandBuffer> commandBuffers;
    VObject<int> obj;
    commandBuffers.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);

    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.commandPool = pool;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandBufferCount = (uint32_t) commandBuffers.size();

    obj.createvk(vkAllocateCommandBuffers(device,
                                     &allocInfo,
                                     commandBuffers.data()));
    return commandBuffers;    
}

uint32_t VulkanModel::findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties, VkPhysicalDeviceMemoryProperties memProperties)
{
    for (uint32_t i = 0; i < memProperties.memoryTypeCount; i++) 
    {
        if ((typeFilter & (1 << i)) && (memProperties.memoryTypes[i].propertyFlags & properties) == properties)
        {
            return i;
        }
    }
    throw std::runtime_error("failed to find suitable memory type!");
}

void VulkanModel::createImage(VkDevice device, uint32_t width, uint32_t height, uint32_t mipLevels, VkSampleCountFlagBits numSamples, VkFormat format, VkImageTiling tiling, VkImageUsageFlags usage, VkMemoryPropertyFlags properties, VkImage& image, VkDeviceMemory& imageMemory, VkPhysicalDeviceMemoryProperties memProperties)
{
    VObject<int> obj;
    VkImageCreateInfo imageInfo{};
    imageInfo.sType = VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO;
    imageInfo.imageType = VK_IMAGE_TYPE_2D;
    imageInfo.extent.width = width;
    imageInfo.extent.height = height;
    imageInfo.extent.depth = 1;
    imageInfo.mipLevels = mipLevels;
    imageInfo.arrayLayers = 1;
    imageInfo.format = format;
    imageInfo.tiling = tiling;
    imageInfo.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    imageInfo.usage = usage;
    imageInfo.samples = numSamples;
    imageInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    obj.createvk(vkCreateImage(device,
                                &imageInfo,
                                nullptr,
                                &image));

    VkMemoryRequirements memRequirements;
    vkGetImageMemoryRequirements(device, image, &memRequirements);

    VkMemoryAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    allocInfo.allocationSize = memRequirements.size;
    allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, properties, memProperties);

    obj.createvk(vkAllocateMemory(device,
                                &allocInfo,
                                nullptr,
                                &imageMemory));

    vkBindImageMemory(device, image, imageMemory, 0);
}


VkImageView createImageView(VkDevice device, VkImage image, VkFormat format, VkImageAspectFlags aspectFlags, uint32_t mipLevels) 
{
    VObject<int> obj;
    VkImageViewCreateInfo viewInfo{};
    viewInfo.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
    viewInfo.image = image;
    viewInfo.viewType = VK_IMAGE_VIEW_TYPE_2D;
    viewInfo.format = format;
    viewInfo.subresourceRange.aspectMask = aspectFlags;
    viewInfo.subresourceRange.baseMipLevel = 0;
    viewInfo.subresourceRange.levelCount = mipLevels;
    viewInfo.subresourceRange.baseArrayLayer = 0;
    viewInfo.subresourceRange.layerCount = 1;

    VkImageView imageView;
    
    obj.createvk(vkCreateImageView(device,
                                &viewInfo,
                                nullptr,
                                &imageView));
    return imageView;
}


VkFormat findSupportedFormat(VkPhysicalDevice pdevice, const std::vector<VkFormat>& candidates, VkImageTiling tiling, VkFormatFeatureFlags features) 
{
    for (VkFormat format : candidates) {
        VkFormatProperties props;
        vkGetPhysicalDeviceFormatProperties(pdevice, format, &props);

        if (tiling == VK_IMAGE_TILING_LINEAR && (props.linearTilingFeatures & features) == features) {
            return format;
        } else if (tiling == VK_IMAGE_TILING_OPTIMAL && (props.optimalTilingFeatures & features) == features) {
            return format;
        }
    }

    throw std::runtime_error("failed to find supported format!");
}

VkFormat findDepthFormat(VkPhysicalDevice pdevice)
{
    return findSupportedFormat(pdevice,
        {VK_FORMAT_D32_SFLOAT, VK_FORMAT_D32_SFLOAT_S8_UINT, VK_FORMAT_D24_UNORM_S8_UINT},
        VK_IMAGE_TILING_OPTIMAL,
        VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT
    );
}

void createColorResources(VkDevice device, VkFormat colorFormat, VkSampleCountFlagBits msaaSamples, VkImage& colorImage, VkDeviceMemory& colorImageMemory, 
                          VkExtent2D extent,  VkPhysicalDeviceMemoryProperties memProperties, uint32_t mipLevels, VkImageView& imageView) 
{
    createImage(device, extent.width, extent.height, 1, msaaSamples, colorFormat, VK_IMAGE_TILING_OPTIMAL, 
                VK_IMAGE_USAGE_TRANSIENT_ATTACHMENT_BIT | VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, 
                colorImage, colorImageMemory, memProperties);
    imageView = createImageView(device, colorImage, colorFormat, VK_IMAGE_ASPECT_COLOR_BIT, mipLevels);
}

void createDepthResources(VkDevice device, VkPhysicalDevice pdevice, VkSampleCountFlagBits msaaSamples, VkImage& depthImage,
                          VkDeviceMemory& depthImageMemory, VkExtent2D extent, VkPhysicalDeviceMemoryProperties memProperties, uint32_t mipLevels,
                          VkImageView& imageView) 
{
    VkFormat depthFormat = findDepthFormat(pdevice);

    createImage(device, extent.width, extent.height, 1, msaaSamples, depthFormat, VK_IMAGE_TILING_OPTIMAL,
                VK_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, depthImage,
                depthImageMemory, memProperties);
    imageView = createImageView(device, depthImage, depthFormat, VK_IMAGE_ASPECT_DEPTH_BIT, mipLevels);
}

void createFramebuffers(VkDevice device, VkExtent2D extent, VkRenderPass renderpass, VkImageView colorImageView, VkImageView depthImageView, std::vector<VkImageView> imageViews, std::vector<VkFramebuffer>& frameBuffers)
{
    VObject<int> obj;
    frameBuffers.resize(imageViews.size());
    for (size_t i = 0; i < imageViews.size(); i++)
    {
        std::array<VkImageView, 3> attachments = {
            colorImageView,
            depthImageView,
            imageViews[i]
        };

        VkFramebufferCreateInfo framebufferInfo{};
        framebufferInfo.sType = VK_STRUCTURE_TYPE_FRAMEBUFFER_CREATE_INFO;
        framebufferInfo.renderPass = renderpass;
        framebufferInfo.attachmentCount = static_cast<uint32_t>(attachments.size());
        framebufferInfo.pAttachments = attachments.data();
        framebufferInfo.width = extent.width;
        framebufferInfo.height = extent.height;
        framebufferInfo.layers = 1;
        obj.createvk(vkCreateFramebuffer(device,
                                    &framebufferInfo,
                                    nullptr,
                                    &frameBuffers[i]));
    }
}

void copyBufferToImage(VkBuffer buffer, VkImage image, uint32_t width, uint32_t height, VkQueue& queue, VkCommandPool& pool, VkDevice device)
{
    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    VkBufferImageCopy region{};
    region.bufferOffset = 0;
    region.bufferRowLength = 0;
    region.bufferImageHeight = 0;
    region.imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    region.imageSubresource.mipLevel = 0;
    region.imageSubresource.baseArrayLayer = 0;
    region.imageSubresource.layerCount = 1;
    region.imageOffset = {0, 0, 0};
    region.imageExtent = {
        width,
        height,
        1
    };
    vkCmdCopyBufferToImage(commandBuffer, buffer, image, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, 1, &region);
    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

void transitionImageLayout(VkImage image, VkFormat format, VkImageLayout oldLayout, VkImageLayout newLayout, uint32_t mipLevels, VkQueue& queue, VkCommandPool& pool, VkDevice device) 
{
    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    VkImageMemoryBarrier barrier{};
    barrier.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
    barrier.oldLayout = oldLayout;
    barrier.newLayout = newLayout;
    barrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.image = image;
    barrier.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    barrier.subresourceRange.baseMipLevel = 0;
    barrier.subresourceRange.levelCount = mipLevels;
    barrier.subresourceRange.baseArrayLayer = 0;
    barrier.subresourceRange.layerCount = 1;

    VkPipelineStageFlags sourceStage;
    VkPipelineStageFlags destinationStage;

    if (oldLayout == VK_IMAGE_LAYOUT_UNDEFINED && newLayout == VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL) 
    {
        barrier.srcAccessMask = 0;
        barrier.dstAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;

        sourceStage = VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT;
        destinationStage = VK_PIPELINE_STAGE_TRANSFER_BIT;
    } 
    else if (oldLayout == VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL && newLayout == VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL) 
    {
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

        sourceStage = VK_PIPELINE_STAGE_TRANSFER_BIT;
        destinationStage = VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT;
    } 
    else 
    {
        throw std::invalid_argument("unsupported layout transition!");
    }

    vkCmdPipelineBarrier(
        commandBuffer,
        sourceStage, destinationStage,
        0,
        0, nullptr,
        0, nullptr,
        1, &barrier
    );

    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

void generateMipmaps(VkFormatProperties formatProperties, VkImage image, VkFormat imageFormat, int32_t texWidth, int32_t texHeight, uint32_t mipLevels, VkQueue& queue, VkCommandPool& pool, VkDevice device) 
{
    // Check if image format supports linear imageFormat
    if (!(formatProperties.optimalTilingFeatures & VK_FORMAT_FEATURE_SAMPLED_IMAGE_FILTER_LINEAR_BIT)) {
        throw std::runtime_error("texture image format does not support linear blitting!");
    }

    VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);

    VkImageMemoryBarrier barrier{};
    barrier.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
    barrier.image = image;
    barrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    barrier.subresourceRange.baseArrayLayer = 0;
    barrier.subresourceRange.layerCount = 1;
    barrier.subresourceRange.levelCount = 1;

    int32_t mipWidth = texWidth;
    int32_t mipHeight = texHeight;

    for (uint32_t i = 1; i < mipLevels; i++) 
    {
        barrier.subresourceRange.baseMipLevel = i - 1;
        barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
        barrier.newLayout = VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL;
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        barrier.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;

        vkCmdPipelineBarrier(commandBuffer,
            VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT, 0,
            0, nullptr,
            0, nullptr,
            1, &barrier);

        VkImageBlit blit{};
        blit.srcOffsets[0] = {0, 0, 0};
        blit.srcOffsets[1] = {mipWidth, mipHeight, 1};
        blit.srcSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        blit.srcSubresource.mipLevel = i - 1;
        blit.srcSubresource.baseArrayLayer = 0;
        blit.srcSubresource.layerCount = 1;
        blit.dstOffsets[0] = {0, 0, 0};
        blit.dstOffsets[1] = { mipWidth > 1 ? mipWidth / 2 : 1, mipHeight > 1 ? mipHeight / 2 : 1, 1 };
        blit.dstSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        blit.dstSubresource.mipLevel = i;
        blit.dstSubresource.baseArrayLayer = 0;
        blit.dstSubresource.layerCount = 1;

        vkCmdBlitImage(commandBuffer,
            image, VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL,
            image, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL,
            1, &blit,
            VK_FILTER_LINEAR);

        barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL;
        barrier.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
        barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

        vkCmdPipelineBarrier(commandBuffer,
            VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT, 0,
            0, nullptr,
            0, nullptr,
            1, &barrier);

        if (mipWidth > 1) mipWidth /= 2;
        if (mipHeight > 1) mipHeight /= 2;
    }

    barrier.subresourceRange.baseMipLevel = mipLevels - 1;
    barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
    barrier.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
    barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
    barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

    vkCmdPipelineBarrier(commandBuffer,
        VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT, 0,
        0, nullptr,
        0, nullptr,
        1, &barrier);

    endSingleTimeCommands(commandBuffer, queue, device, pool);
}

void createBuffer(VkDevice device, VkDeviceSize size, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties, VkBuffer& buffer, VkDeviceMemory& bufferMemory, VkPhysicalDeviceMemoryProperties memProperties) 
{
    VkBufferCreateInfo bufferInfo{};
    bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    bufferInfo.size = size;
    bufferInfo.usage = usage;
    bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    if (vkCreateBuffer(device, &bufferInfo, nullptr, &buffer) != VK_SUCCESS) {
        throw std::runtime_error("failed to create buffer!");
    }

    VkMemoryRequirements memRequirements;
    vkGetBufferMemoryRequirements(device, buffer, &memRequirements);

    VkMemoryAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    allocInfo.allocationSize = memRequirements.size;
    allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, properties, memProperties);

    if (vkAllocateMemory(device, &allocInfo, nullptr, &bufferMemory) != VK_SUCCESS) {
        throw std::runtime_error("failed to allocate buffer memory!");
    }

    vkBindBufferMemory(device, buffer, bufferMemory, 0);
}

void createTextureImage(VkPhysicalDevice pdevice, VkDevice device, std::string texture, VkQueue& queue, VkCommandPool& pool, 
                        VkPhysicalDeviceMemoryProperties memProperties, VkImage& textureImage, VkDeviceMemory& textureImageMemory, uint32_t& mipLevels)
{
    int texWidth, texHeight, texChannels;
    // loadTexture();
    stbi_uc* pixels = stbi_load(texture.c_str(), &texWidth, &texHeight, &texChannels, STBI_rgb_alpha);
    VkDeviceSize imageSize = texWidth * texHeight * 4;
    mipLevels = static_cast<uint32_t>(std::floor(std::log2(std::max(texWidth, texHeight)))) + 1;
    if (!pixels)
    {
        throw std::runtime_error("failed to load texture image!");
    }
    VkBuffer stagingBuffer;
    VkDeviceMemory stagingBufferMemory;
    createBuffer(device, imageSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
    void* data;
    vkMapMemory(device, stagingBufferMemory, 0, imageSize, 0, &data);
        memcpy(data, pixels, static_cast<size_t>(imageSize));
    vkUnmapMemory(device, stagingBufferMemory);
    stbi_image_free(pixels);
    createImage(device, texWidth, texHeight, mipLevels, VK_SAMPLE_COUNT_1_BIT, VK_FORMAT_R8G8B8A8_SRGB, VK_IMAGE_TILING_OPTIMAL, VK_IMAGE_USAGE_TRANSFER_SRC_BIT | VK_IMAGE_USAGE_TRANSFER_DST_BIT | VK_IMAGE_USAGE_SAMPLED_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, textureImage, textureImageMemory, memProperties);
    transitionImageLayout(textureImage, VK_FORMAT_R8G8B8A8_SRGB, VK_IMAGE_LAYOUT_UNDEFINED, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, mipLevels, queue, pool, device);
    copyBufferToImage(stagingBuffer, textureImage, static_cast<uint32_t>(texWidth), static_cast<uint32_t>(texHeight), queue, pool, device);
    //transitioned to VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL while generating mipmaps
    vkDestroyBuffer(device, stagingBuffer, nullptr);
    vkFreeMemory(device, stagingBufferMemory, nullptr);
    VkFormatProperties formatProperties;
    VkFormat imageFormat = VK_FORMAT_R8G8B8A8_SRGB;
    vkGetPhysicalDeviceFormatProperties(pdevice, imageFormat, &formatProperties);
    generateMipmaps(formatProperties, textureImage, VK_FORMAT_R8G8B8A8_SRGB, texWidth, texHeight, mipLevels, queue, pool, device);
}

void createTextureImageView(VkDevice device, VkImage textureImage, uint32_t mipLevels, VkImageView& textureImageView, VkFormat format = VK_FORMAT_R8G8B8A8_SRGB, VkImageAspectFlagBits aspectFlags = VK_IMAGE_ASPECT_COLOR_BIT)
{
    textureImageView = createImageView(device, textureImage, format, aspectFlags, mipLevels);
}

void createTextureSampler(VkPhysicalDeviceProperties properties, VkDevice device, VkSampler& textureSampler)
{
    VObject<int> obj;
    VkSamplerCreateInfo samplerInfo{};
    samplerInfo.sType = VK_STRUCTURE_TYPE_SAMPLER_CREATE_INFO;
    samplerInfo.magFilter = VK_FILTER_LINEAR;
    samplerInfo.minFilter = VK_FILTER_LINEAR;
    samplerInfo.addressModeU = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    samplerInfo.addressModeV = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    samplerInfo.addressModeW = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    samplerInfo.anisotropyEnable = VK_TRUE;
    samplerInfo.maxAnisotropy = properties.limits.maxSamplerAnisotropy;
    samplerInfo.borderColor = VK_BORDER_COLOR_INT_OPAQUE_BLACK;
    samplerInfo.unnormalizedCoordinates = VK_FALSE;
    samplerInfo.compareEnable = VK_FALSE;
    samplerInfo.compareOp = VK_COMPARE_OP_ALWAYS;
    samplerInfo.mipmapMode = VK_SAMPLER_MIPMAP_MODE_LINEAR;
    samplerInfo.minLod = 0.0f;
    samplerInfo.maxLod = VK_LOD_CLAMP_NONE;
    samplerInfo.mipLodBias = 0.0f;
    obj.createvk(vkCreateSampler(device,
                                &samplerInfo,
                                nullptr,
                                &textureSampler));
}

// // void loadModel()
// // {
// // }

void createCommandBuffers(VkDevice device, VkCommandPool& pool,  std::vector<VkCommandBuffer>& commandBuffers) 
{
    commandBuffers.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.commandPool = pool;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandBufferCount = (uint32_t) commandBuffers.size();

    if (vkAllocateCommandBuffers(device, &allocInfo, commandBuffers.data()) != VK_SUCCESS) {
        throw std::runtime_error("failed to allocate command buffers!");
    }
}

void createSyncObjects(std::vector<VkSemaphore>& imageAvailableSemaphores, std::vector<VkSemaphore>& renderFinishedSemaphores, std::vector<VkFence>& inFlightFences, VkDevice device)
{
    imageAvailableSemaphores.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
    renderFinishedSemaphores.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
    inFlightFences.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);

    VkSemaphoreCreateInfo semaphoreInfo{};
    semaphoreInfo.sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO;

    VkFenceCreateInfo fenceInfo{};
    fenceInfo.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
    fenceInfo.flags = VK_FENCE_CREATE_SIGNALED_BIT;

    for (size_t i = 0; i < ogun::constants::MAX_FRAMES_IN_FLIGHT; i++) {
        if (vkCreateSemaphore(device, &semaphoreInfo, nullptr, &imageAvailableSemaphores[i]) != VK_SUCCESS ||
            vkCreateSemaphore(device, &semaphoreInfo, nullptr, &renderFinishedSemaphores[i]) != VK_SUCCESS ||
            vkCreateFence(device, &fenceInfo, nullptr, &inFlightFences[i]) != VK_SUCCESS) {
            throw std::runtime_error("failed to create synchronization objects for a frame!");
        }
    }
}

void recordCommandBuffer(VkCommandBuffer& commandBuffer, uint32_t imageIndex, VkRenderPass renderpass, VkExtent2D extent, VkFramebuffer framebuffer,
                         VkPipeline pipeline, std::vector<VkBuffer> vertexBuffers, VkBuffer indexBuffer, VkPipelineLayout layout, std::vector<VkDescriptorSet> descriptorsets,
                         uint32_t indicesCount, uint32_t vertsCount, VkDevice device, std::vector<VertexShaderData> vertices, std::vector<uint16_t> indices,
                         VkQueue& queue, VkCommandPool commandPool,  VkPhysicalDeviceMemoryProperties memProperties)
{
    // /*****************************************************************************************************/
    // VkBuffer vertexBuffer;
    // VkDeviceMemory vertexBufferMemory;
    // VkDeviceSize bufferSize = sizeof(vertices[0]) * vertices.size();

    // VkBuffer stagingBuffer;
    // VkDeviceMemory stagingBufferMemory;

    // //******** createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
    // VkBufferCreateInfo bufferInfo{};
    // bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    // bufferInfo.size = bufferSize;
    // bufferInfo.usage = VK_BUFFER_USAGE_TRANSFER_SRC_BIT;
    // bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    // if (vkCreateBuffer(device, &bufferInfo, nullptr, &stagingBuffer) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to create buffer!");
    // }

    // VkMemoryRequirements memRequirements;
    // vkGetBufferMemoryRequirements(device, stagingBuffer, &memRequirements);

    // VkMemoryAllocateInfo allocInfo{};
    // allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    // allocInfo.allocationSize = memRequirements.size;
    // allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, memProperties);

    // if (vkAllocateMemory(device, &allocInfo, nullptr, &stagingBufferMemory) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to allocate buffer memory!");
    // }

    // vkBindBufferMemory(device, stagingBuffer, stagingBufferMemory, 0);


    // void* data;
    // vkMapMemory(device, stagingBufferMemory, 0, bufferSize, 0, &data);
    //     memcpy(data, vertices.data(), (size_t) bufferSize);
    // vkUnmapMemory(device, stagingBufferMemory);


    // //******** createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, vertexBuffer, vertexBufferMemory, memProperties);
    // // VkBufferCreateInfo bufferInfo{};
    // bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    // bufferInfo.size = bufferSize;
    // bufferInfo.usage = VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT;
    // bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;

    // if (vkCreateBuffer(device, &bufferInfo, nullptr, &vertexBuffer) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to create buffer!");
    // }

    // VkMemoryRequirements tmemRequirements;
    // vkGetBufferMemoryRequirements(device, vertexBuffer, &tmemRequirements);

    // VkMemoryAllocateInfo tallocInfo{};
    // tallocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    // tallocInfo.allocationSize = tmemRequirements.size;
    // tallocInfo.memoryTypeIndex = findMemoryType(tmemRequirements.memoryTypeBits, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, memProperties);

    // if (vkAllocateMemory(device, &tallocInfo, nullptr, &vertexBufferMemory) != VK_SUCCESS) {
    //     throw std::runtime_error("failed to allocate buffer memory!");
    // }

    // vkBindBufferMemory(device, vertexBuffer, vertexBufferMemory, 0);


    //  //******** copyBuffer(stagingBuffer, vertexBuffer, bufferSize, queue, device, pool);
    // //******** VkCommandBuffer commandBuffer = beginSingleTimeCommands(pool, device);
    // VkCommandBuffer zcommandBuffer;

    // VkCommandBufferAllocateInfo zallocInfo{};
    // zallocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    // zallocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    // zallocInfo.commandPool = commandPool;
    // zallocInfo.commandBufferCount = 1;

    // // VkCommandBuffer commandBuffer;
    // vkAllocateCommandBuffers(device, &zallocInfo, &zcommandBuffer);

    // VkCommandBufferBeginInfo beginInfo{};
    // beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    // beginInfo.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;

    // vkBeginCommandBuffer(zcommandBuffer, &beginInfo);

    // // return commandBuffer;

    // VkBufferCopy copyRegion{};
    // copyRegion.srcOffset = 0; // Optional
    // copyRegion.dstOffset = 0; // Optional
    // copyRegion.size = bufferSize;
    // vkCmdCopyBuffer(zcommandBuffer,stagingBuffer, vertexBuffer, 1, &copyRegion);

    // //******** endSingleTimeCommands(commandBuffer, queue, device, commandPool);
    // vkEndCommandBuffer(zcommandBuffer);
    // VkSubmitInfo submitInfo{};
    // submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    // submitInfo.commandBufferCount = 1;
    // submitInfo.pCommandBuffers = &zcommandBuffer;
    // VkResult result = vkQueueSubmit(queue, 1, &submitInfo, VK_NULL_HANDLE);
    // vkQueueWaitIdle(queue);
    // vkFreeCommandBuffers(device, commandPool, 1, &zcommandBuffer);


    // vkDestroyBuffer(device, stagingBuffer, nullptr);
    // vkFreeMemory(device, stagingBufferMemory, nullptr);
    // std::vector<VkBuffer> m_vertexBuffers;
    // m_vertexBuffers.push_back(vertexBuffer);


    // // /*****************************************************************************************************/


    VkCommandBufferBeginInfo zbeginInfo{};
    zbeginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;

    if (vkBeginCommandBuffer(commandBuffer, &zbeginInfo) != VK_SUCCESS) {
        throw std::runtime_error("failed to begin recording command buffer!");
    }

    VkRenderPassBeginInfo renderPassInfo{};
    renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;
    renderPassInfo.renderPass = renderpass;
    renderPassInfo.framebuffer = framebuffer;
    renderPassInfo.renderArea.offset = {0, 0};
    renderPassInfo.renderArea.extent = extent;

    std::array<VkClearValue, 2> clearValues{};
    clearValues[0].color = {{0.0f, 0.0f, 0.0f, 1.0f}};
    clearValues[1].depthStencil = {1.0f, 1u};

    renderPassInfo.clearValueCount = static_cast<uint32_t>(clearValues.size());
    renderPassInfo.pClearValues = clearValues.data();

    vkCmdBeginRenderPass(commandBuffer, &renderPassInfo, VK_SUBPASS_CONTENTS_INLINE);

        vkCmdBindPipeline(commandBuffer, VK_PIPELINE_BIND_POINT_GRAPHICS, pipeline);

        VkViewport viewport{};
        viewport.x = 0.0f;
        viewport.y = 0.0f;
        viewport.width = (float) extent.width;
        viewport.height = (float) extent.height;
        viewport.minDepth = 0.0f;
        viewport.maxDepth = 1.0f;
        vkCmdSetViewport(commandBuffer, 0, 1, &viewport);

        VkRect2D scissor{};
        scissor.offset = {0, 0};
        scissor.extent = extent;
        vkCmdSetScissor(commandBuffer, 0, 1, &scissor);

        VkDeviceSize offsets[] = {0};
        vkCmdBindVertexBuffers(commandBuffer, 0, vertexBuffers.size(), vertexBuffers.data(), offsets);

        vkCmdBindIndexBuffer(commandBuffer, indexBuffer, 0, VK_INDEX_TYPE_UINT16);

        vkCmdBindDescriptorSets(commandBuffer, VK_PIPELINE_BIND_POINT_GRAPHICS, layout, 0, descriptorsets.size(), descriptorsets.data(), 0, nullptr);

        vkCmdDrawIndexed(commandBuffer, static_cast<uint32_t>(indicesCount), 1, 0, 0, 0);
        
        vkCmdDraw(commandBuffer, static_cast<uint32_t>(vertices.size()), 1, 0, 0);

    vkCmdEndRenderPass(commandBuffer);

    if (vkEndCommandBuffer(commandBuffer) != VK_SUCCESS)
    {
        throw std::runtime_error("failed to record command buffer!");
    }
}




static VKAPI_ATTR VkBool32 VKAPI_CALL debugCallback(VkDebugUtilsMessageSeverityFlagBitsEXT messageSeverity, VkDebugUtilsMessageTypeFlagsEXT messageType, const VkDebugUtilsMessengerCallbackDataEXT* pCallbackData, void* pUserData) {
    std::cerr << "validation layer: " << pCallbackData->pMessage << std::endl;

    return VK_FALSE;
}

VkResult CreateDebugUtilsMessengerEXT(VkInstance instance, const VkDebugUtilsMessengerCreateInfoEXT* pCreateInfo, const VkAllocationCallbacks* pAllocator, VkDebugUtilsMessengerEXT* pDebugMessenger) {
    auto func = (PFN_vkCreateDebugUtilsMessengerEXT) vkGetInstanceProcAddr(instance, "vkCreateDebugUtilsMessengerEXT");
    if (func != nullptr) {
        return func(instance, pCreateInfo, pAllocator, pDebugMessenger);
    } else {
        return VK_ERROR_EXTENSION_NOT_PRESENT;
    }
}

void populateDebugMessengerCreateInfo(VkDebugUtilsMessengerCreateInfoEXT& createInfo) {
    createInfo = {};
    createInfo.sType = VK_STRUCTURE_TYPE_DEBUG_UTILS_MESSENGER_CREATE_INFO_EXT;
    createInfo.messageSeverity = VK_DEBUG_UTILS_MESSAGE_SEVERITY_VERBOSE_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_SEVERITY_WARNING_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_SEVERITY_ERROR_BIT_EXT;
    createInfo.messageType = VK_DEBUG_UTILS_MESSAGE_TYPE_GENERAL_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_TYPE_VALIDATION_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_TYPE_PERFORMANCE_BIT_EXT;
    createInfo.pfnUserCallback = debugCallback;
}


void setupDebugMessenger(bool enableValidationLayers, VkInstance instance, VkDebugUtilsMessengerEXT& debugMessenger) 
{
    if (!enableValidationLayers) return;

    VkDebugUtilsMessengerCreateInfoEXT createInfo;
    populateDebugMessengerCreateInfo(createInfo);

    VkResult result = CreateDebugUtilsMessengerEXT(instance, &createInfo, nullptr, &debugMessenger);
    if (result != VK_SUCCESS) {
        throw std::runtime_error("failed to set up debug messenger!");
    }
}




// // void append(std::vector<VertexShaderData>& vertices, std::vector<uint16_t>& indices)
// // {
// //     for (auto vert : vertices)
// //     {
// //         verts.push_back(vert);
// //     }
    
// //     for (auto ind : indices)
// //     {
// //         inds.push_back(ind);
// //     }
// // }




/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef Vertex_h
#define Vertex_h

#include <cstddef>
#include <array>
#include <vector>
#include <Eigen/Dense>

namespace ogun
{
    
struct VertexShaderData
{
    glm::vec3 position;
    glm::vec4 color;
    glm::vec2 texture;
    glm::vec3 normal;

    static std::vector<VkVertexInputBindingDescription> bindingDescription()
    {
        std::vector<VkVertexInputBindingDescription> bindingDescriptions{};
        bindingDescriptions.resize(1);
        bindingDescriptions[0].binding = 0;
        bindingDescriptions[0].stride = sizeof(VertexShaderData);
        bindingDescriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
        return bindingDescriptions;
    }

    static std::array<VkVertexInputAttributeDescription, 4> attributeDescription()
    {
        std::array<VkVertexInputAttributeDescription, 4> attributeDescriptions{};
        attributeDescriptions[0].binding = 0;
        attributeDescriptions[0].location = 0;
        attributeDescriptions[0].format = VK_FORMAT_R32G32B32_SFLOAT;
        attributeDescriptions[0].offset = offsetof(VertexShaderData, position);

        attributeDescriptions[1].binding = 0;
        attributeDescriptions[1].location = 1;
        attributeDescriptions[1].format = VK_FORMAT_R32G32B32A32_SFLOAT;
        attributeDescriptions[1].offset = offsetof(VertexShaderData, color);

        attributeDescriptions[2].binding = 0;
        attributeDescriptions[2].location = 2;
        attributeDescriptions[2].format = VK_FORMAT_R32G32_SFLOAT;
        attributeDescriptions[2].offset = offsetof(VertexShaderData, texture);

        attributeDescriptions[3].binding = 0;
        attributeDescriptions[3].location = 3;
        attributeDescriptions[3].format = VK_FORMAT_R32G32B32_SFLOAT;
        attributeDescriptions[3].offset = offsetof(VertexShaderData, normal);

        // std::array<VkVertexInputAttributeDescription, 4> attributeDescriptions{};
        // attributeDescriptions[1].binding = 0;
        // attributeDescriptions[1].location = 1;
        // attributeDescriptions[1].format = VK_FORMAT_R32G32B32A32_SFLOAT;
        // attributeDescriptions[1].offset = offsetof(VertexShaderData, color);
    
        // attributeDescriptions[3].binding = 0;
        // attributeDescriptions[3].location = 3;
        // attributeDescriptions[3].format = VK_FORMAT_R32G32_SFLOAT;
        // attributeDescriptions[3].offset = offsetof(VertexShaderData, texture);

        return attributeDescriptions;
    }

    bool operator==(const VertexShaderData& other) const 
    {
        return position == other.position && color == other.color; // && normal == other.normal && texture == other.texture;
    }
};

//     // tell Vulkan how to pass this data format to the vertex shader once it's been uploaded into GPU memory
//     struct Vertex
//     {
//         Eigen::Vector3d position;
//         Eigen::Vector3d color;
//         Eigen::Vector3d normal;

//         // vertex binding describes at which rate to load data from memory throughout the vertices. It specifies
//         // the number of bytes between data entries and whether to move to the next data entry after each vertex or
//         // after each instance.
//         static std::vector<VkVertexInputBindingDescription> bindingDescriptions()
//         {
//             std::vector<VkVertexInputBindingDescription> bindingDescriptions{};
//             bindingDescriptions.resize(1);

//             // per-vertex data is packed together in one array, so we're only going to have one binding. The binding
//             // parameter specifies the index of the binding in the array of bindings. The stride parameter specifies
//             // the number of bytes from one entry to the next, and the inputRate parameter can have one of the
//             // following values:
//             //     VK_VERTEX_INPUT_RATE_VERTEX  : Move to the next data entry after each vertex
//             //     VK_VERTEX_INPUT_RATE_INSTANCE: Move to the next data entry after each instance
//             // We're not going to use instanced rendering, so we'll stick to per-vertex data
//             bindingDescriptions[0].binding = 0;
//             bindingDescriptions[0].stride = sizeof(Vertex);
//             bindingDescriptions[0].inputRate = VK_VERTEX_INPUT_RATE_VERTEX;
//             return bindingDescriptions;
//         }

//         // describes how to handle vertex input is VkVertexInputAttributeDescription
//         static std::array<VkVertexInputAttributeDescription, 3> attributeDescriptions()
//         {
//             std::array<VkVertexInputAttributeDescription, 3> attributeDescriptions{};

//             // As the function prototype indicates, there are going to be two of these structures. An attribute description
//             //      struct describes how to extract a vertex attribute from a chunk of vertex data originating from a binding
//             //      description. We have two attributes, position and color, so we need two attribute description structs.
//             //      The binding parameter tells Vulkan from which binding the per-vertex data comes. The location parameter references
//             //      the location directive of the input in the vertex shader. The input in the vertex shader with location 0 is the position
//             //      which has two 32-bit float components.
//             // The format parameter describes the type of data for the attribute. A bit confusingly, the formats are specified
//             //      using the same enumeration as color formats. The following shader types and formats are commonly used together:
//             //     float: VK_FORMAT_R32_SFLOAT
//             //     vec2 : VK_FORMAT_R32G32_SFLOAT
//             //     vec3 : VK_FORMAT_R32G32B32_SFLOAT
//             //     vec4 : VK_FORMAT_R32G32B32A32_SFLOAT
//             attributeDescriptions[0].binding = 0;
//             attributeDescriptions[0].location = 0;
//             attributeDescriptions[0].format = VK_FORMAT_R32G32B32_SFLOAT;
//             attributeDescriptions[0].offset = offsetof(Vertex, position);

//             // As you can see, you should use the format where the amount of color channels matches the number of components in the shader data type.
//             // It is allowed to use more channels than the number of components in the shader, but they will be silently discarded. If the number of
//             // channels is lower than the number of components, then the BGA components will use default values of (0, 0, 1). The color type (SFLOAT, UINT, SINT)
//             // and bit width should also match the type of the shader input. See the following examples:
//             //         ivec2 : VK_FORMAT_R32G32_SINT, a 2-component vector of 32-bit signed integers
//             //         uvec4 : VK_FORMAT_R32G32B32A32_UINT, a 4-component vector of 32-bit unsigned integers
//             //         double: VK_FORMAT_R64_SFLOAT, a double-precision (64-bit) float
//             // The format parameter implicitly defines the byte size of attribute data and the offset parameter specifies the number of bytes since
//             // the start of the per-vertex data to read from. The binding is loading one Vertex at a time and the position attribute (pos) is at an
//             // offset of 0 bytes from the beginning of this struct. This is automatically calculated using the offsetof macro.
//             attributeDescriptions[1].binding = 0;
//             attributeDescriptions[1].location = 1;
//             attributeDescriptions[1].format = VK_FORMAT_R32G32B32_SFLOAT;
//             attributeDescriptions[1].offset = offsetof(Vertex, color);

//             // normal
//             attributeDescriptions[2].binding = 0;
//             attributeDescriptions[2].location = 2;
//             attributeDescriptions[2].format = VK_FORMAT_R32G32B32_SFLOAT;
//             attributeDescriptions[2].offset = offsetof(Vertex, normal);
//             return attributeDescriptions;
//         }
//     };

//     struct RenderObjectIndices
//     {
//         alignas(4)  int light;
//     };
} // namespace ogun

#endif // Vertex_h





        // Respond to the message:
        // handleSize(hwnd, (UINT)wParam, width, height);
        // std::cout << "window resized" << std::endl;
        // freq = (int) wParam;
        // // std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
        // switch(freq)
        // {
        //     case SIZE_RESTORED:
        //         std::cout << "w restored" << std::endl;
        //     case SIZE_MINIMIZED:
        //         std::cout << "w minimized" << std::endl;
        //     case SIZE_MAXIMIZED:
        //         std::cout << " maximized" << std::endl;
        //     case SIZE_MAXSHOW:
        //         std::cout << " show" << std::endl;
        //     case SIZE_MAXHIDE:
        //         std::cout << " hide" << std::endl;
        //     default:
        //         break;
        // }
    // case WM_CREATE:
    //     std::cout << "window created" << std::endl;
    //     std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
    // case WM_MOVE:
    //     std::cout << "window moved " << std::endl;
    //     std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
    // case WM_CLOSE:
    //     std::cout << "window closed" << std::endl;
    //     PostQuitMessage(0);
    //     return 0;
    // case WM_SHOWWINDOW:
    //     std::cout << "window show" << std::endl;
    //     std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
    // case WM_MOUSEHOVER:
    //     std::cout << " window hover " << std::endl;
    


        std::wstring widestr = std::wstring(data.name.begin(), data.name.end());
    const wchar_t* name = widestr.c_str();
    hesabu::HWindow* window = new hesabu::HWindow();
    uint32_t status = 0;
    uint32_t nCmdShow = 1;
    if (!window->Create(name, WS_OVERLAPPEDWINDOW))
    {
        status = 1;
    }


    


    
        case VK_HOME:
            // Process the HOME key. 
            break; 

        case VK_END:
            // Process the END key. 
            break; 

        case VK_INSERT:
            // Process the INS key. 
            break; 

        case VK_DELETE:
            // Process the DEL key. 
            break; 

        case VK_F2:
            // Process the F2 key. 
            break; 






/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "HWindow.h"
#include <iostream>
#include "vulkan_exec.h"

using namespace hesabu;

HWindow::HWindow()
    : HBaseWindow("")
{
    model = new ogun::VulkanModel();
}

void HWindow::init()
{
    ogun::VulkanModelInfo info;
    info.window.hwnd = m_hwnd;
    info.window.name = m_name;
    info.window.height = 800;
    info.window.width = 600;
    info.mount = "D:";
    // info.shaderLibraryPath = "D:/dev/projects/ogun/assets/shaders";
    // info.shaderLibraryPath = "D:/dev/projects/v0.0.1/ogunv2/ogun/assets/shaders";
    model->init(info);
}

void HWindow::update()
{
    static auto startTime = std::chrono::high_resolution_clock::now();
    auto currentTime = std::chrono::high_resolution_clock::now();
    float tick = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();
    model->draw(tick);
}


void HWindow::handleKeyPress(WPARAM wParam)
{
    switch (wParam)
    {
        case VK_NUMPAD1:
            std::cout << "Fill polygon mode" << std::endl;
            break;
            
        case VK_NUMPAD2:
            std::cout << "Wire frame polygon mode" << std::endl;
            break;
            
        case VK_NUMPAD3:
            std::cout << "Point polygon mode" << std::endl;
            break;

        case 'R':
            std::cout << "Recompiling shaders..." << std::endl;
            model->recompileShaders();
            break;

        case 'U':
            model->update(1.0f, glm::vec3(0.0f, 0.0f, 1.0f));
            break;

        case 'D':
            model->update(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f));
            break;

        case VK_LEFT:
            model->update(1.0f, glm::vec3(1.0f, 0.0f, 0.0f));
            break; 

        case VK_RIGHT:
            model->update(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f));
            break; 
        
        case VK_UP:
            model->update(1.0f, glm::vec3(0.0f, 1.0f, 0.0f));
            break; 

        case VK_DOWN:
            model->update(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f));
            break; 

        default: 
            // Process other non-character keystrokes. 
            break; 
    }
};
LRESULT HWindow::HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    switch (uMsg)
    {
    case WM_KEYDOWN:
        handleKeyPress(wParam);
    default:
        break;
    }

    switch (uMsg)
    {
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    case WM_SIZE:
    {
        uint32_t width = LOWORD(lParam);  // Macro to get the low-order word.
        uint32_t height = HIWORD(lParam); // Macro to get the high-order word.

        if (bSize == false)
        {
            bSize = true;   
        }
        else
        {   
            // Respond to the message:
            handleSize((UINT)wParam, width, height);
        }
    }
    case WM_PAINT:
        if (!bInit)
        {
            init();
            bInit = true;
        }
        else
        {
            update();
        }
        // update();
        // std::cout << " paint ! " << std::endl;
        // {
        //     PAINTSTRUCT ps;
        //     HDC hdc = BeginPaint(m_hwnd, &ps);
        //     FillRect(hdc, &ps.rcPaint, (HBRUSH) (COLOR_WINDOW+1));
        //     EndPaint(m_hwnd, &ps);
        // }
        return 0;
    default:
        return DefWindowProc(m_hwnd, uMsg, wParam, lParam);
    }

    return TRUE;
}

void HWindow::handleSize(UINT flag, int width, int height)
{
    // std::cout << "window resized : w - h " << width << " - " << height << std::endl;
    model->resizeFramebuffer(width, height);
    // std::cout << " resized flag " << flag << std::endl;
    // if (flag == SIZE_RESTORED)
    // {
    //     std::cout << "restored" << std::endl;
    // }
    // else if (flag == SIZE_MINIMIZED)
    // {
    //     std::cout << "minimized" << std::endl;
    // }
    // else if (flag == SIZE_MAXIMIZED)
    // {
    //     std::cout << "maximized" << std::endl;
    // }
    // else if (flag == SIZE_MAXSHOW)
    // {
    //     std::cout << "show" << std::endl;
    // }
    // else if (flag == SIZE_MAXHIDE)
    // {
    //     std::cout << "hide" << std::endl;
    // }
    // else {}
}




    // std::vector<VertexShaderData> verts = {}; // meshbuffer->vertices(); // = square1->vertices();
    // std::vector<uint16_t> inds = {}; // meshbuffer->indices(); // = square1->indices();

    // for (auto vert: cube0->vertices())
    // {
    //     verts.push_back(vert);
    // }
    // for (auto ind: cube0->indices())
    // {
    //     inds.push_back(ind);
    // }

    // for (auto vert: cube1->vertices())
    // {
    //     verts.push_back(vert);
    // }
    // for (auto ind: cube1->indices())
    // {
    //     inds.push_back(ind + 24);
    // }
    
    // for (auto vert: cube2->vertices())
    // {
    //     verts.push_back(vert);
    // }
    // for (auto ind: cube2->indices())
    // {
    //     inds.push_back(ind + 24 + 24);
    // }

    // for (auto vert: sq0->vertices())
    // {
    //     verts.push_back(vert);
    // }
    // for (auto ind: sq0->indices())
    // {
    //     inds.push_back(ind+24);
    // }

    // for (auto vert: sq1->vertices())
    // {
    //     verts.push_back(vert);
    // }
    // for (auto ind: sq1->indices())
    // {
    //     inds.push_back(ind + 24 + 4);
    // }

    // for (auto vert: square2->vertices())
    // {
    //     verts.push_back(vert);
    // }
    // for (auto ind: square2->indices())
    // {
    //     inds.push_back(ind + 8);
    // }

    // for (auto vert: s3->vertices())
    // {
    //     verts.push_back(vert);
    // }
    // for (auto ind: s3->indices())
    // {
    //     inds.push_back(ind + 8);
    // }
    
    // verts.resize(verts.size() + square0->vertices().size());
    // inds.resize(inds.size() + square0->indices().size());

    // verts.insert(verts.end(), square0->vertices().begin(), square0->vertices().end());
    // inds.insert(inds.end(), square0->indices().begin(), square0->indices().end());


    