/**
 * @copyright DEFAULT
 * @brief: VWindow wrapper class
 * @note : N/A
 */

#include "VWindow.h"
#include "Logger.h"
#include <SDL2/SDL.h>
#include <SDL2/SDL_vulkan.h>

using namespace RenderEngine;

VWindow::VWindow()
{}

VWindow::VWindow(VkInstance instance)
    : m_name("Vulkan Engine")
    , m_logunit("VWindow")
    , m_created(false)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    m_extent.height = DEFAULT_WINDOW_HEIGHT;
    m_extent.width = DEFAULT_WINDOW_WIDTH;
    create(instance);
}

VWindow::~VWindow() {}

bool VWindow::create(VkInstance instance)
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Creating window " << LoggingTool::Logger::endl;

    bool created;
    swtich(WindowAPIType)
    {
        case GLFW:
            m_created = createGLFWWindow(instance, &m_surface);
        case SDL:
            m_created = createSDLWindow(instance, &m_surface);
        default:
            // No window type selected to create
            m_created = NULL;
            break;
    }
    return m_created;
}

bool VWindow::createGLFWWindow(VkInstance instance, VkSurfaceKHR &surface)
{
    glfwInit();

    glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
    GLFWwindow* window = glfwCreateWindow(
        m_extent.width,
        m_extent.height,
        m_name.c_str(),
        nullptr,
        nullptr
    );

    VkWin32SurfaceCreateInfoKHR createInfoKHR{};
    createInfoKHR.sType = VK_STRUCTURE_TYPE_WIN32_SURFACE_CREATE_INFO_KHR;
    createInfoKHR.hwnd = glfwGetWin32Window(window);
    createInfoKHR.hinstance = GetModuleHandle(nullptr);

    VkResult vkWin32SurfaceKHRCreated = vkCreateWin32SurfaceKHR(instance, &createInfoKHR, nullptr, &surface);
}

bool VWindow::createSDLWindow(VkInstance instance)
{
    // initialize SDL and create a window with it.
    SDL_Init(SDL_INIT_VIDEO);
    SDL_WindowFlags window_flags = (SDL_WindowFlags)(SDL_WINDOW_VULKAN);

    // struct SDL_Window* m_window;
    m_window = SDL_CreateWindow(
        m_name.c_str(),
        SDL_WINDOWPOS_UNDEFINED,
        SDL_WINDOWPOS_UNDEFINED,
        m_extent.width,
        m_extent.height,
        window_flags
    );

    // Create the surface
    SDL_Vulkan_CreateSurface(m_window, instance, &m_surface);

    // Get initial window attributes
    SDL_Vulkan_GetDrawableSize(m_window, &(int)m_extentPixels.width, &(int)m_extentPixels.height);
}

struct SDL_Window* VWindow::hwnd()
{
    return m_window;
}

VkSurfaceKHR VWindow::surface()
{
    return m_surface;
}  

VkExtent2D VWindow::extent()
{
    return m_extent;
}

VkExtent2D VWindow::extentPixels()
{
    return m_extentPixels;
}
