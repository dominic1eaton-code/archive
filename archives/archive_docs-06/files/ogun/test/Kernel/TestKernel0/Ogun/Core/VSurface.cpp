/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VSurface.h"

using namespace ogun;

VSurface& VSurface::hwnd(HWND hwnd)
{
    m_hwnd = hwnd;
    return *this;
}

VSurface& VSurface::build(VkInstance instance)
{
    m_createInfo.sType = VK_STRUCTURE_TYPE_WIN32_SURFACE_CREATE_INFO_KHR;
    m_createInfo.hwnd = m_hwnd;
    m_createInfo.hinstance = GetModuleHandle(nullptr);

    createVk(vkCreateWin32SurfaceKHR(instance,
                                     &m_createInfo,
                                     nullptr,
                                     &m_surface));

    return *this;
}