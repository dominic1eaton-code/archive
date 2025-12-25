/**
 * @license
 * @brief core vulkan objects
 */
#ifndef vulkan_model_h
#define vulkan_model_h

#include <string>
#include <filesystem>
#include <stdint.h>
#include <vector>
#include "vulkan_core.h"
#include <windows.h>

namespace ogun
{

    enum class Platform
    {
        WINDOWS,
        ANDROID,
        IOS,
        LINUX
    };

    struct Version
    {
        Version() : Version(1, 0, 0, 0) {}

        Version(uint32_t maj, uint32_t min, uint32_t pat, uint32_t ext)
            : major(maj), minor(min), patch(pat), extra(ext)
        {
        }

        Version(uint32_t maj, uint32_t min, uint32_t pat)
            : Version(maj, min, pat, 0)
        {
        }

        uint32_t major;
        uint32_t minor;
        uint32_t patch;
        uint32_t extra;
    };

    struct ModelConfiguration
    {
        std::string name;
        Platform platform;
        Version version;
    };

    struct VModelParams
    {
        std::string assetPath = "";
    };

    struct VModelConfiguration
    {
        uint32_t DEFAULT_MSAA_SAMPLES = 1;
    };

    enum class ImageTypes
    {
        DEPTH,
        COLOR,
        TEXTURE
    };

    struct HWindow
    {
        HWND hwnd;
        HINSTANCE instance = GetModuleHandle(nullptr);
        VkExtent2D extent;
    };

    struct OgInstance
    {
        std::vector<const char *> extensions = {"VK_KHR_surface", "VK_KHR_win32_surface", "VK_EXT_debug_utils"};
        // std::vector<const char*> layers = {"VK_LAYER_KHRONOS_validation"};
        std::vector<const char *> layers = {};
        VkApplicationInfo appinfo;
        VkInstanceCreateInfo createinfo;
        VkInstance instance;
    };

    struct OgPipeline
    {
    };

    struct OgModel
    {
        ogun::ModelConfiguration model_configuration;
        OgInstance oginstance;
        VkDebugUtilsMessengerEXT _debugger = VK_NULL_HANDLE;
        VkSurfaceKHR _surface = VK_NULL_HANDLE;
        VkInstance _instance = VK_NULL_HANDLE;
        VkPhysicalDevice _physical_device = VK_NULL_HANDLE;
        VkDevice _logical_device = VK_NULL_HANDLE;
        bool enable_validation = false;
        std::vector<VkPipeline> _pipelines = {};
        VkQueue _graphics_queue = VK_NULL_HANDLE;
        VkQueue _present_queue = VK_NULL_HANDLE;
        VkSwapchainKHR _swapchain = VK_NULL_HANDLE;
        VkFormat _swapchain_image_format;
        VkExtent2D _swapchain_extent;
        std::vector<VkImage> _swapchain_images;
        std::vector<VkImageView> _swapchain_image_views;
        VkRenderPass _render_pass = VK_NULL_HANDLE;
        std::vector<VkImage> _color_images;
        std::vector<VkDeviceMemory> _color_image_memories;
        std::vector<VkImageView> _color_image_views;
        std::vector<VkImage> _depth_images;
        std::vector<VkDeviceMemory> _depth_image_memories;
        std::vector<VkImageView> _depth_image_views;
        std::vector<VkFramebuffer> _offscreen_framebuffers;
        std::vector<VkBuffer> _vertex_buffers;
        std::vector<VkBuffer> _index_buffers;
        std::vector<VkBuffer> _stage_buffers;
        std::vector<VkFramebuffer> _framebuffers;
        VkCommandPool _command_pool = VK_NULL_HANDLE;
        std::vector<VkCommandBuffer> _command_buffers;
        VkSemaphore _image_available_semaphore = VK_NULL_HANDLE;
        VkSemaphore _render_finished_semaphore = VK_NULL_HANDLE;
        VkFence _in_flight_fence = VK_NULL_HANDLE;
    };

    void init_model();
    void run_model();
    void shutdown_model();
    void draw_frame();

    void create_instance(std::string name, Version version);
    void create_debug_messenger();
    void create_surface(Platform platform, HWindow window);
    void select_physical_device();
    void create_logical_device();
    void create_queue();
    void create_graphics_pipeline();
    void create_compute_pipeline();
    void create_raytracing_pipeline();
    void create_pipeline();
    void create_swapchain();
    void create_fence();
    void create_semaphore();
    void create_descriptor();
    void create_framebuffer();
    void create_renderpass();
    void create_command();
    void create_commandpool();

    void create_buffer();
    void create_index_buffer();
    void create_vertex_buffer();
    void create_staging_buffer();
    void create_uniform_buffer();
    void create_storage_buffer();
    void create_command_buffer();

    void create_image(ImageTypes type);
    void create_sampler();
    void create_material();
    void create_texture();
}; // namespace ogun

#endif // vulkan_model_h