/**
 * @copyright DEFAULT
 * @brief: VWindow wrapper class
 * @note : N/A
 */

#include "VWindow.h"
#include "Logger.h"

using namespace RenderEngine;

VWindow::VWindow()
    : m_logunit("VWindow")
    , m_window()
    , m_name("Vulkan Engine")
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();

    m_extent.height = DEFAULT_WINDOW_HEIGHT;
    m_extent.width = DEFAULT_WINDOW_WIDTH;
}

VWindow::~VWindow() {}

struct SDL_Window* VWindow::hwnd()
{
    return m_window;
}

bool VWindow::create()
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Creating window " << LoggingTool::Logger::endl;

    // We initialize SDL and create a window with it.
    SDL_Init(SDL_INIT_VIDEO);
    SDL_WindowFlags window_flags = (SDL_WindowFlags)(SDL_WINDOW_VULKAN);

    m_window = SDL_CreateWindow(
        m_name.c_str(),
        SDL_WINDOWPOS_UNDEFINED,
        SDL_WINDOWPOS_UNDEFINED,
        m_extent.width,
        m_extent.height,
        window_flags
    );
    return true;
}
