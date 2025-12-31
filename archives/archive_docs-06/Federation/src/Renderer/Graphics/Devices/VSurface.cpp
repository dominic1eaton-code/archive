/**
 * @copyright DEFAULT
 * @brief: VSurface wrapper class
 * @note : N/A
 */

#include "VSurface.h"
#include "Logger.h"
#include <SDL2/SDL_vulkan.h>
#include <limits>       // Necessary for std::numeric_limits
#include <algorithm>    // Necessary for std::clamp

using namespace RenderEngine;

VSurface::VSurface()
    : m_logunit("VSurface")
    , m_surface(VK_NULL_HANDLE)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

VSurface::~VSurface() {}

bool VSurface::create(VkInstance instance, VkPhysicalDevice device, SDL_Window* window)
{
    // if(SDL2)
    // Create the surface
    SDL_Vulkan_CreateSurface(window, instance, &m_surface);

    // Just checking if a swap chain is available is not sufficient, 
    // because it may not actually be compatible with our window surface. 
    // Creating a swap chain also involves a lot more settings than instance 
    // and device creation, so we need to query for some more details before 
    // we're able to proceed

    // Check for presentation support
    // vkGetPhysicalDeviceSurfaceSupportKHR(device, i, surface, &m_presentSupport);
    
    // query surface attributes and capabilities
    vkGetPhysicalDeviceSurfaceCapabilitiesKHR(device, m_surface, m_capabilities);

    // query the supported surface formats
    uint32_t formatCount;
    vkGetPhysicalDeviceSurfaceFormatsKHR(device, m_surface, &formatCount, nullptr);

    if (formatCount != 0) 
    {
        details.formats.resize(formatCount);
        vkGetPhysicalDeviceSurfaceFormatsKHR(device, m_surface, &formatCount, details.formats.data());
    }

    // query the supported presentation modes 
    uint32_t presentModeCount;
    vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &presentModeCount, nullptr);

    if (presentModeCount != 0) 
    {
        details.presentModes.resize(presentModeCount);
        vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &presentModeCount, details.presentModes.data());
    }

    // if the swapChainAdequate conditions were met then the support is
    // definitely sufficient, but there may still be many different modes
    // of varying optimality. find the right settings for the best possible
    // swap chain

    return true;
}