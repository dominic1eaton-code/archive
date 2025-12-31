/**
 * @copyright DEFAULT
 * @brief: Generic Window wrapper class
 * @note : N/A
 */
#include "VWindow.h"

VWindow::VWindow()
    : m_width(DEFAULT_WINDOW_WIDTH)
    , m_height(DEFAULT_WINDOW_HEIGHT)
{}

VWindow::~VWindow()
{}

bool VWindow::create()
{
    m_logger->log("VWindow", LoggingLevel::INFO) << "Creating new application window" << VulkanLogger::endl;
    bool windowCreated = false;

    switch(m_windowType)
    {
        // Create glfw window if supported
        case WindowType::GLFW:
            windowCreated = createGLFWWindow();
            break;
        // Create sdl window if supported
        case WindowType::SDL:
            windowCreated = createSDLWWindow();
            break;
        // No window type selected to create
        default:
            windowCreated = false;
            break;
    }

    return windowCreated;
}

bool VWindow::createGLFWWindow()
{
        // Vulkan does not have a context and the Vulkan instance 
        // is created via the Vulkan API itself. Disable context
        // creation by setting the GLFW_CLIENT_API hint to 
        // GLFW_NO_API. see https://www.glfw.org/docs/3.3/context_guide.html
        glfwWindowHint(GLFW_CLIENT_API, GLFW_NO_API);
        m_window =  glfwCreateWindow(m_width, 
                                    m_height, 
                                    m_windowName,
                                    nullptr, 
                                    nullptr);
        m_surface->initialize(m_instance, m_window);
        m_internalSurface = m_surface->create();
        m_extent.width = static_cast<uint32_t>(m_width);
        m_extent.height = static_cast<uint32_t>(m_height);
    
    // check if window was created
    if(m_window)
        return true;
    else
        return false;
}

bool VWindow::createSDLWWindow()
{
    m_window = SDL_CreateWindow(
        m_windowName,
        SDL_WINDOWPOS_UNDEFINED,
        SDL_WINDOWPOS_UNDEFINED,
        m_extent.width
        m_extent.height,
        window_flags
    );
    
    // check if window was created
    if(m_window)
        return true;
    else
        return false;
}

