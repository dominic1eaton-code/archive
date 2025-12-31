/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef vulkan_model_h
#define vulkan_model_h

#include <filesystem>
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
#include "Ogun/Core/Vertex.h"


#define VK_USE_PLATFORM_WIN32_KHR

namespace ogun
{

struct TVertex;

class VulkanModelSupport
{
public:
    VulkanModelSupport() = default;
    virtual ~VulkanModelSupport(void) = default;

    static VkCommandBuffer beginSingleTimeCommands(VkCommandPool commandPool, VkDevice device);

    static void endSingleTimeCommands(VkCommandBuffer& commandBuffer, VkQueue& queue, VkDevice device, VkCommandPool& pool);

    static void copyBuffer(VkBuffer srcBuffer, VkBuffer dstBuffer, VkDeviceSize size, VkQueue& queue, VkDevice device, VkCommandPool& pool, VkDeviceSize srcOffset = 0, VkDeviceSize dstOffset = 0);

    static void createBuffer(VkDevice device, VkDeviceSize size, VkBufferUsageFlags usage, VkMemoryPropertyFlags properties, VkBuffer& buffer, VkDeviceMemory& bufferMemory, VkPhysicalDeviceMemoryProperties memProperties);

    static VkCommandPool createCommandPool(VkDevice device, std::optional<uint32_t> index);

    static std::vector<VkCommandBuffer> createCommandBuffers(VkDevice device, VkCommandPool pool);

    static uint32_t findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties, VkPhysicalDeviceMemoryProperties memProperties);

    static void createImage(VkDevice device, uint32_t width, uint32_t height, uint32_t mipLevels, VkSampleCountFlagBits numSamples, VkFormat format, VkImageTiling tiling, VkImageUsageFlags usage, VkMemoryPropertyFlags properties, VkImage& image, VkDeviceMemory& imageMemory, VkPhysicalDeviceMemoryProperties memProperties);

    static VkImageView createImageView(VkDevice device, VkImage image, VkFormat format, VkImageAspectFlags aspectFlags, uint32_t mipLevels);

    static VkFormat findSupportedFormat(VkPhysicalDevice pdevice, const std::vector<VkFormat>& candidates, VkImageTiling tiling, VkFormatFeatureFlags features);

    static VkFormat findDepthFormat(VkPhysicalDevice pdevice);

    static void createColorResources(VkDevice device, VkFormat colorFormat, VkSampleCountFlagBits msaaSamples, VkImage& colorImage, VkDeviceMemory& colorImageMemory, 
                              VkExtent2D extent,  VkPhysicalDeviceMemoryProperties memProperties, uint32_t mipLevels, VkImageView& imageView);

    static void createDepthResources(VkDevice device, VkPhysicalDevice pdevice, VkSampleCountFlagBits msaaSamples, VkImage& depthImage,
                              VkDeviceMemory& depthImageMemory, VkExtent2D extent, VkPhysicalDeviceMemoryProperties memProperties, uint32_t mipLevels,
                              VkImageView& imageView);

    static void createFramebuffers(VkDevice device, VkExtent2D extent, VkRenderPass renderpass, VkImageView colorImageView, VkImageView depthImageView, std::vector<VkImageView> imageViews, std::vector<VkFramebuffer>& frameBuffers);

    static void copyBufferToImage(VkBuffer buffer, VkImage image, uint32_t width, uint32_t height, VkQueue& queue, VkCommandPool& pool, VkDevice device);

    static void transitionImageLayout(VkImage image, VkFormat format, VkImageLayout oldLayout, VkImageLayout newLayout, uint32_t mipLevels, VkQueue& queue, VkCommandPool& pool, VkDevice device);

    static void generateMipmaps(VkFormatProperties formatProperties, VkImage image, VkFormat imageFormat, int32_t texWidth, int32_t texHeight, uint32_t mipLevels, VkQueue& queue, VkCommandPool& pool, VkDevice device);

    static glm::vec2 createTextureImage(VkPhysicalDevice pdevice, VkDevice device, std::string texture, VkQueue& queue, VkCommandPool& pool,
                            VkPhysicalDeviceMemoryProperties memProperties, VkImage& textureImage, VkDeviceMemory& textureImageMemory, uint32_t& mipLevels);

    static void createTextureImageView(VkDevice device, VkImage textureImage, uint32_t mipLevels, VkImageView& textureImageView, VkFormat format = VK_FORMAT_R8G8B8A8_SRGB, VkImageAspectFlagBits aspectFlags = VK_IMAGE_ASPECT_COLOR_BIT);

    static void createTextureSampler(VkPhysicalDeviceProperties properties, VkDevice device, VkSampler& textureSampler);

    static void createCommandBuffers(VkDevice device, VkCommandPool& pool,  std::vector<VkCommandBuffer>& commandBuffers);

    static void createSyncObjects(std::vector<VkSemaphore>& imageAvailableSemaphores, std::vector<VkSemaphore>& renderFinishedSemaphores, std::vector<VkFence>& inFlightFences, VkDevice device);

    static void recordCommandBuffer(VkCommandBuffer& commandBuffer, uint32_t imageIndex, VkRenderPass renderpass, VkExtent2D extent, VkFramebuffer framebuffer,
                         VkPipeline pipeline, std::vector<VkBuffer> vertexBuffers, VkBuffer indexBuffer, VkPipelineLayout layout, std::vector<VkDescriptorSet> descriptorsets,
                         uint32_t indicesCount, uint32_t vertsCount, VkDevice device, std::vector<TVertex> vertices, std::vector<uint16_t> indices,
                         VkQueue& queue, VkCommandPool commandPool,  VkPhysicalDeviceMemoryProperties memProperties);

    static VKAPI_ATTR VkBool32 VKAPI_CALL debugCallback(VkDebugUtilsMessageSeverityFlagBitsEXT messageSeverity, VkDebugUtilsMessageTypeFlagsEXT messageType, const VkDebugUtilsMessengerCallbackDataEXT* pCallbackData, void* pUserData);
 
    static VkResult CreateDebugUtilsMessengerEXT(VkInstance instance, const VkDebugUtilsMessengerCreateInfoEXT* pCreateInfo, const VkAllocationCallbacks* pAllocator, VkDebugUtilsMessengerEXT* pDebugMessenger);

    static void populateDebugMessengerCreateInfo(VkDebugUtilsMessengerCreateInfoEXT& createInfo);
 
    static void setupDebugMessenger(bool enableValidationLayers, VkInstance instance, VkDebugUtilsMessengerEXT& debugMessenger);
};

}; // namespace ogun

#endif // vulkan_model_h