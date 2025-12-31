/**
 * @copyright
 * @brief
 * @note
 */
#pragma once
#ifndef vulkan_model_h
#define vulkan_model_h

#include <vulkan/vulkan.h>
#include <vector>
#include <optional>
#include <Windows.h>
#include <filesystem>
#include <fstream>
#include "ogun_scene.h"


namespace vulkan
{

namespace constants
{
    const uint32_t MAX_FRAMES_IN_FLIGHT = 3;
};

struct PDeviceInfo
{
    VkPhysicalDeviceProperties properties;
    VkPhysicalDeviceFeatures features;
    VkPhysicalDeviceMemoryProperties memoryProperties;
    std::vector<VkQueueFamilyProperties> queueFamiliesProperties;
    uint32_t queueFamilyPropertyCount;
    VkSampleCountFlagBits msaa_samples;
    uint32_t formatCount;
    uint32_t presentModeCount;
    VkSurfaceCapabilitiesKHR capabilities;
    std::vector<VkSurfaceFormatKHR> formats;
    VkFormat depth_format;
    VkImageTiling tiling;
    VkFormatFeatureFlags formatFeatures;
    std::vector<VkFormatProperties> formatProperties;
    std::vector<VkPresentModeKHR> present_modes;
    VkBool32 presentSupport;
    uint32_t rating;
    std::vector<const char*> extensions;
    uint32_t extensionsCount;
};

struct QueueFamilyIndices
{
    std::optional<uint32_t> graphics;
    std::optional<uint32_t> present;
    std::optional<uint32_t> compute;
    std::optional<uint32_t> transfer;
    std::optional<uint32_t> sparse;
    VkQueueFlags supported = {};

    // generic self check that device has full capabilities
    bool isComplete()
    {
        return graphics.has_value() &&
               present.has_value() &&
               compute.has_value() &&
               transfer.has_value() &&
               sparse.has_value();
    }
};

struct PDevice
{
    VkPhysicalDevice device;
    PDeviceInfo pinfo;
    std::vector<VkDeviceQueueCreateInfo> qinfo;
};

struct PSwapchainSupport
{

};

struct PSwapchainInfo
{
    VkFormat dformat;
    std::vector<VkSurfaceFormatKHR> formats;
    VkExtent2D extent;
    std::vector<VkPresentModeKHR> present_modes;
    VkSurfaceCapabilitiesKHR capabilities;
};

struct PSwapchain
{
    VkSwapchainKHR buffer;
    VkFormat format;
    std::vector<VkImageView> views;
    VkExtent2D extent;
};

struct VRenderpassInfo
{
    VkFormat iformat;
    VkFormat dformat;
    VkSampleCountFlagBits msaa_samples;
    VkPipelineBindPoint bpoint;
    std::vector<bool> hasAttachments;
};

struct VHeightMap
{

};

struct VFont
{

};

struct VImage
{
    VkImage img;
    VkImageView view;
    VkDeviceMemory memory;
};

struct VImageInfo
{
    uint32_t mipLevels;
    VkExtent2D extent;
    VkFormat format;
    VkImageAspectFlags aspect;
    VkImageTiling tiling;
    VkSampleCountFlagBits samples;
    VkImageUsageFlags usage;
};

struct VTexture
{
    VkDescriptorImageInfo info;
    uint32_t id;
    std::string file;
};

struct VSingleCommand
{
    VkDevice device;
    VkCommandPool pool;
    VkQueue queue;
};

struct VDeviceMemoryInfo
{
    VkMemoryPropertyFlags flags;
    VkPhysicalDeviceMemoryProperties properties;
};

struct VPipeline
{
    VkPipeline pipeline;
    VkPipelineLayout layout;
    VkPipelineBindPoint bpoint;
};

struct VPipelineInfo
{
    VkPolygonMode pmode;
    VkSampleCountFlagBits samples;
    std::vector<VkDynamicState> dynamics_states;
    VkPrimitiveTopology topology;
};

struct VShaderModule
{
    VkShaderStageFlagBits stage;
    VkShaderModule module;
    const char* entry_name;
};

struct VBuffer
{
    VkBuffer buffer;
    VkDeviceMemory memory;
    void* data;
    uint32_t id;
    uint32_t size;
};

struct VBufferInfo
{
    VkBufferUsageFlags usage;
    VkDeviceSize size;
    VkDeviceSize offset;
};

struct VDynamicState
{
    bool viewport;
    bool scissor;
    bool primitive_topology;
};

struct VShaderObjectInfo
{
    VkDescriptorType type;
    VkDeviceSize size;
    VkShaderStageFlagBits stage;
    VkBufferUsageFlagBits usage;
    VkDescriptorSetLayoutBinding binding;
    VkDescriptorPoolSize pool;
    VkWriteDescriptorSet write;
};

struct VShaderObject
{
    VkDescriptorSet set;
    VBuffer buffer;
    VShaderObjectInfo info;
};

struct VDescriptor
{
    VkDescriptorSetLayout layout;
    std::vector<VkDescriptorSet> sets;
};

struct SwapchainSupport
{
};

struct VSkybox
{
    // id
    // cube map
    // texture map
};

inline const uint32_t TERRAIN_PATCH_VERTICES = 4u; // number of vertices per patch
struct VTerrain
{
    uint32_t resolution = 20u;
    std::vector<sema::Vertex> vertices;
    uint32_t width;
    uint32_t height;
};

struct VModel
{
    VkDevice device;
    VkQueue queue;
    VkCommandPool pool;
    VkExtent2D extent;
    uint32_t frame_index;
    std::vector<std::vector<VkFence>> fences;
    std::vector<std::vector<VkSemaphore>> semaphores;
    VkSwapchainKHR swapchain;
    std::vector<std::vector<VkCommandBuffer>> cmds;
    std::vector<VkRenderPass> renderpasses;
    std::vector<std::vector<VkFramebuffer>> framebuffers;
};

struct VPipelineProperties
{
    VkPrimitiveTopology topology;
};
struct VMaterial
{
    VPipeline pipeline;
    VkPipelineLayout layout;
    VDynamicState dynamic_states;
    VDescriptor descriptor;
    uint32_t id;
    bool indexed;
    VPipelineProperties properties;
};

struct VPushConstant
{
    VkShaderStageFlags stage;
    uint32_t offset;
    uint32_t size;
    const void* pValues;
};

struct VScene
{
    // std::vector<ogun::GPUCamera> cameras;
    std::vector<ogun::GPUScene> scenes;
    std::vector<ogun::GPULight> lights;
    std::vector<VBuffer> stage_buffers;
    std::vector<std::vector<VBuffer>> vertex_buffers;
    std::vector<VBuffer> index_buffers;
    std::vector<std::vector<VBuffer>> shader_buffers;
    std::vector<VMaterial> materials;
    std::vector<VPushConstant> push_constants;
    std::vector<VImage> images;
    ogun::VCamera primary_camera;
    std::vector<ogun::GPUParticle> particles;
};

struct VCursor
{
    float x;
    float y;
};
struct VFrame
{
    VScene scene;
    VModel model;
    bool resized;
    VkExtent2D window_extent;
    glm::vec2 cursor;
    std::vector<bool> passes_enabled;
};

struct VAxis
{
    glm::vec3 normal;
    glm::vec3 tangent;
    glm::vec3 bitangent;
};

const std::vector<VkSampleCountFlagBits> DEFAULT_STAGE_FLAG_BITS = {
    VK_SAMPLE_COUNT_64_BIT, VK_SAMPLE_COUNT_32_BIT,
    VK_SAMPLE_COUNT_16_BIT, VK_SAMPLE_COUNT_8_BIT,
    VK_SAMPLE_COUNT_4_BIT,  VK_SAMPLE_COUNT_2_BIT
};

const std::vector<VkFormat> DEPTH_FORMAT_CANDIDATES = {
    VK_FORMAT_D32_SFLOAT, VK_FORMAT_D32_SFLOAT_S8_UINT, VK_FORMAT_D24_UNORM_S8_UINT
};

const VkDeviceSize fixed_buffer_size = 1000000;
const uint32_t MAX_LIGHTS_COUNT = 10;
const uint32_t MAX_TEXTURES_COUNT = 10;

void create_instance(VkInstance& instance, std::vector<const char*> extensions, std::vector<const char*> layers);
void create_debugger(VkInstance instance, VkDebugUtilsMessengerEXT& debugMessenger);
void create_surface_win32(VkSurfaceKHR& surface, VkInstance instance, HWND hwnd);
void create_surface_android();
void create_surface_xwindow();
void create_surface_wayland();
void create_physical_device(PDevice& pdevice, VkInstance instance, VkSurfaceKHR surface);
void create_logical_device(VkDevice& ldevice, std::vector<VkQueue>& queues, VkPhysicalDevice pdevice, VkPhysicalDeviceFeatures features, std::vector<VkDeviceQueueCreateInfo> queue_info, std::vector<const char*> extensions);
void create_swapchain(PSwapchain& swapchain, PSwapchainInfo info, VkDevice device, VkSurfaceKHR surface);
void create_renderpass(VkRenderPass& renderpass, VkDevice device, VRenderpassInfo info);
void create_fence(std::vector<VkFence>& fences, VkFenceCreateFlagBits flags, VkDevice device);
void create_semaphore(std::vector<VkSemaphore>& semaphores, VkDevice device);
void create_command_pool(VkCommandPool& command_pool, VkDevice device, std::optional<uint32_t> gindex);
void create_command_buffer(std::vector<VkCommandBuffer>& command_buffers, VkDevice device, VkCommandPool pool);
void create_shader_modules();
void create_descriptor_layout(VkDescriptorSetLayout& layout, VkDevice device, std::vector<VkDescriptorSetLayoutBinding> bindings);
void create_graphics_pipeline(VPipeline& pipeline, VPipelineInfo info, VkDevice device, VkRenderPass renderpass, VkPipelineLayout pipeline_layout, std::vector<VShaderModule> shaders, sema::VertexType vertex_type);
void create_framebuffer(std::vector<VkFramebuffer>& fbuffers, VkDevice device, VkRenderPass renderpass, VkExtent2D extent, std::vector<VkImageView> simages, std::vector<VkImageView> aimages);
void create_descriptor(VDescriptor& descriptor, std::vector<std::vector<VBuffer>>& shader_buffers, std::vector<VkDescriptorImageInfo> textures, VkDevice device, VkPhysicalDeviceMemoryProperties mproperties);
void create_compute_descriptor(VDescriptor& descriptor, std::vector<std::vector<VBuffer>>& shader_buffers, std::vector<VkDescriptorImageInfo> textures, VkDevice device, VkPhysicalDeviceMemoryProperties mproperties);
void create_buffer(VBuffer& buffer, VkDevice device, VBufferInfo info, VDeviceMemoryInfo minfo);
void create_image(VImage& image, VkDevice device, VImageInfo info, VDeviceMemoryInfo minfo);
void create_color_image(VImage& image, VkExtent2D extent, VkFormat format, VkSampleCountFlagBits samples, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device);
void create_depth_image(VImage& image, VkExtent2D extent, VkFormat format, VkSampleCountFlagBits samples, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device);
void create_imageview(std::vector<VkImageView>& views, VkDevice device, std::vector<VkImage> images, VkFormat format, VkImageAspectFlags aspectFlags, uint32_t mipLevels);
void create_font(VFont& font);
void create_heightmap(VHeightMap& height_map);
void create_shader_objects(std::vector<VShaderObject>& shaderobjects);
void create_vertex_buffer(VBuffer& buffer, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device);
void create_index_buffer(VBuffer& buffer, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device);
void create_uniform_buffer(std::vector<VBuffer>& buffers, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device);
void create_storage_buffer(std::vector<VBuffer>& buffers, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device);
void create_stage_buffer(VBuffer& buffer, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device);
void create_texture_image(VkDescriptorImageInfo& texture, std::string texture_file, VBuffer& stage_buffer, VkPhysicalDevice pdevice, VkPhysicalDeviceMemoryProperties mproperties, VSingleCommand scmd, float maxSamplerAnisotropy, bool empty = false);
void create_image_sampler(VkSampler& sampler,  VkDevice device, VkPhysicalDeviceProperties properties);
void create_pipeline_layout(VkPipelineLayout& layout, std::vector<VkDescriptorSetLayout> descriptor_layouts, VkDevice device);
void create_push_constant();
void create_compute_pipeline(VPipeline& pipeline, VkPipelineLayout pipeline_layout, std::vector<VShaderModule> shaders, VkDevice device);
void create_raytracing_pipeline(VPipeline& pipeline, VkPipelineLayout pipeline_layout, std::vector<VShaderModule> shaders, VkDevice device);

void record_draw_commands(std::vector<VkCommandBuffer>& cmds, uint32_t image_index, std::vector<VkRenderPass> renderpass, std::vector<std::vector<VkFramebuffer>> framebuffer, VkExtent2D extent, VScene scene, std::vector<bool> passes_enabled);
void record_compute_commands(std::vector<VkCommandBuffer>& cmds, uint32_t image_index, std::vector<VkRenderPass> renderpass, std::vector<std::vector<VkFramebuffer>> framebuffer, VkExtent2D extent, VScene scene);
void rebuild_swapchain(VkExtent2D extent);
void retrieve_texture_image(VImage& image, VkExtent2D extent, VBuffer& stage_buffer, VSingleCommand scmd);
void load_resources(std::filesystem::path asset_library_path);
void load_textures(std::vector<VkDescriptorImageInfo>& textures, std::filesystem::path asset_library_path, VBuffer stage_buffer, VkPhysicalDevice pdevice, VkPhysicalDeviceMemoryProperties mproperties, VSingleCommand scmd, float maxSamplerAnisotropy);
void copy_buffer(VkBuffer srcBuffer, VkBuffer dstBuffer, VkDeviceSize size, VkDeviceSize srcOffset, VkDeviceSize dstOffset, VSingleCommand& scmd);
void copy_image2buffer(VkImage& image, VkBuffer& buffer, VkExtent2D copy_extent, VSingleCommand& scmd);
void copy_buffer2image(VkBuffer buffer, VkImage image, VkExtent2D copy_extent, VSingleCommand scmd);
void transition_image_layout(VkImage image, VkImageLayout old_layout, VkImageLayout new_layout, uint32_t mip_levels, VSingleCommand scmd);
void generate_mipmap(VkImage image, VkFormatProperties format_properties, uint32_t mip_levels, VkExtent2D texture_extent, VSingleCommand scmd);
VkCommandBuffer begin_single_command(VkCommandPool pool, VkDevice device);
void end_single_command(VkCommandBuffer buffer, VkQueue queue, VkCommandPool pool, VkDevice device);
void checkvk(VkResult result);
void query_pdevice_info(VkPhysicalDevice device,  VkSurfaceKHR surface, PDeviceInfo* deviceInfo);
void query_pdevice_queue_info(VkPhysicalDevice device,  VkSurfaceKHR surface, std::vector<VkQueueFamilyProperties> queueFamiliesProperties, std::vector<VkDeviceQueueCreateInfo>& queueInfo);
uint32_t rate_pdevice(PDeviceInfo info, std::vector<VkDeviceQueueCreateInfo> queueInfo);
VkSampleCountFlagBits maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties);
VkSurfaceFormatKHR select_swapchain_surface_format(const std::vector<VkSurfaceFormatKHR>& availableFormats);
VkPresentModeKHR select_swapchain_present_modes(const std::vector<VkPresentModeKHR>& availablepresent_modes);
VkExtent2D select_swapchain_extent(const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent);
VkFormat find_depth_format(VkPhysicalDevice pdevice);
VkFormat find_support_format(VkPhysicalDevice pdevice, const std::vector<VkFormat>& candidates, VkImageTiling tiling, VkFormatFeatureFlags features);
uint32_t findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties, VkPhysicalDeviceMemoryProperties memProperties);
void load_shader_files(std::vector<VShaderModule>& shaders, std::filesystem::path asset_library_path, std::string package, std::string module, VkDevice device);
std::vector<char> readFile(const std::string& filename);
VKAPI_ATTR VkBool32 VKAPI_CALL debugCallback(VkDebugUtilsMessageSeverityFlagBitsEXT messageSeverity, VkDebugUtilsMessageTypeFlagsEXT messageType, const VkDebugUtilsMessengerCallbackDataEXT* pCallbackData, void* pUserData);
VkResult CreateDebugUtilsMessengerEXT(VkInstance instance, const VkDebugUtilsMessengerCreateInfoEXT* pCreateInfo, const VkAllocationCallbacks* pAllocator, VkDebugUtilsMessengerEXT* pDebugMessenger);
void update_shaders(float tick, uint32_t image_index, std::vector<std::vector<VBuffer>> shader_buffers, ogun::VCamera primary_camera, ogun::GPUScene scene, glm::vec2 cursor);

template<typename T>
void copy_buffer_data(VBuffer srcbuffer, std::vector<VBuffer>& destbuffer, std::vector<T> copy_data, uint32_t soffset, uint32_t doffset, VSingleCommand& scmd)
{
    VkDeviceSize buffersize = sizeof(copy_data[0]) * copy_data.size();
    void* data;
    vkMapMemory(scmd.device, srcbuffer.memory, 0, buffersize, 0, &data);
        memcpy(data, copy_data.data(), (size_t)buffersize);
    vkUnmapMemory(scmd.device, srcbuffer.memory);
    for (int i = 0; i < destbuffer.size(); i++)
        copy_buffer(srcbuffer.buffer, destbuffer[i].buffer, buffersize, soffset, doffset, scmd);
//    vkFreeMemory(device, srcbuffer.memory, nullptr);
}

template <typename T> int sgn(T val)
{
    return (T(0) < val) - (val < T(0));
}

}; //  namespace vulkan

#endif // vulkan_model_h