/**
 * @license
 * @brief core vulkan objects
 */

#include "vulkan_model.h"
#include "vulkan_scene.h"
#include <vulkan/vulkan_win32.h>

ogun::OgInstance oginstance;
// ogun::ModelConfiguration* model_configuration = new ogun::ModelConfiguration();
ogun::ModelConfiguration model_configuration;
VkDebugUtilsMessengerEXT _debugger = VK_NULL_HANDLE;
VkSurfaceKHR _surface = VK_NULL_HANDLE;
VkInstance _instance = VK_NULL_HANDLE;
VkPhysicalDevice _physical_device = VK_NULL_HANDLE;
VkDevice _logical_device = VK_NULL_HANDLE; 
bool enable_validation = false;


void ogun::init_model()
{
    model_configuration.name = "TestEngine";
    model_configuration.platform = Platform::WINDOWS;
    model_configuration.version = Version(1, 1, 0);
    HWindow window;

    /* devices */
    create_instance(model_configuration.name, model_configuration.version);
    create_surface(model_configuration.platform, window);
    select_physical_device();
    create_logical_device();
    create_swapchain();
    create_renderpass();
    create_commandpool();
    create_command_buffer();

    /* resources */
    create_image(ImageTypes::TEXTURE);
    create_image(ImageTypes::COLOR);
    create_image(ImageTypes::DEPTH);

    create_framebuffer();
    create_fence();
    create_semaphore();

    /* scene */
    uint32_t default_sceneID = 0;
    load_scene(default_sceneID);

    /* pipelines */
    std::vector<OgPipeline> _pipelines;
    // for (auto pipeline : _pipelines)
    //     create_pipeline(pipeline.info);
    create_pipeline(); // render opaque objects
    create_pipeline(); // render lines
    create_pipeline(); // render particles
    create_pipeline(); // compute particles
    create_pipeline(); // render offscreen pass

    /* sync */
    create_fence(); // render fence
    create_fence(); // compute fence
    create_semaphore();
    create_semaphore();
}

void ogun::run_model()
{
    draw_frame();
}

void ogun::shutdown_model()
{
}

void ogun::draw_frame()
{
}

void ogun::create_image(ImageTypes type)
{
}

void ogun::create_instance(std::string name, Version version)
{
    oginstance.appinfo.pNext = NULL;
    oginstance.appinfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    oginstance.appinfo.pApplicationName = name.c_str();
    oginstance.appinfo.applicationVersion = VK_MAKE_VERSION(1, 1, 0);
    oginstance.appinfo.pEngineName = name.c_str();
    oginstance.appinfo.engineVersion = VK_MAKE_VERSION(1, 1, 0);
    oginstance.appinfo.apiVersion = VK_MAKE_API_VERSION(0, 1, 1, 0);

    oginstance.createinfo.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
    oginstance.createinfo.pNext = NULL;
    oginstance.createinfo.flags = 0;
    oginstance.createinfo.pApplicationInfo = &oginstance.appinfo;
    oginstance.createinfo.enabledExtensionCount = oginstance.extensions.size();
    oginstance.createinfo.ppEnabledExtensionNames = oginstance.extensions.data();
    oginstance.createinfo.enabledLayerCount = oginstance.layers.size();
    oginstance.createinfo.ppEnabledLayerNames = oginstance.layers.data();

    ogun::validatevk(vkCreateInstance(
        &oginstance.createinfo,
        nullptr,
        &oginstance.instance));
}

void ogun::create_debug_messenger()
{
}

void ogun::create_surface(Platform platform, HWindow window)
{
    assert(oginstance.instance && "create instance before creating surface!");
    assert((platform == Platform::WINDOWS) && "only windows platform is supported currently!");
    assert((window.hwnd != NULL) && "invalid window handle!");
    assert((window.instance != NULL) && "invalid window instance!");
    assert((window.extent.width > 0 && window.extent.height > 0) && "invalid window extent!");
    assert((_surface == VK_NULL_HANDLE) && "surface already created!");

    switch (platform)
    {
    case Platform::WINDOWS:
    {
        VkWin32SurfaceCreateInfoKHR createinfo;
        createinfo.sType = VK_STRUCTURE_TYPE_WIN32_SURFACE_CREATE_INFO_KHR;
        createinfo.pNext = NULL;
        createinfo.flags = 0;
        createinfo.hwnd = window.hwnd;
        createinfo.hinstance = window.instance;
        ogun::validatevk(vkCreateWin32SurfaceKHR(
            _instance,
            &createinfo,
            nullptr,
            &_surface));
        break;
    };
    case Platform::ANDROID:
        break;
    case Platform::IOS:
        break;
    case Platform::LINUX:
        break;
    default:
        break;
    }
}

void ogun::select_physical_device()
{
}

void ogun::create_logical_device()
{
}

void ogun::create_queue()
{
}

void ogun::create_pipeline()
{
}

void ogun::create_swapchain()
{
}

void ogun::create_renderpass()
{
}

void ogun::create_commandpool()
{
}

void ogun::create_command_buffer()
{
}

void ogun::create_framebuffer()
{
}

void ogun::create_fence()
{
}

void ogun::create_semaphore()
{
}

void ogun::create_descriptor()
{
}