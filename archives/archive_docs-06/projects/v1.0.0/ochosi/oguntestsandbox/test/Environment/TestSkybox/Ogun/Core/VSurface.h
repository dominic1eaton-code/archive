/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VSurface_h
#define VSurface_h

#include "VObject.h"
#include <vulkan/vulkan_win32.h>

namespace ogun
{

class VSurface : public VObject<VSurface>
{
public:
    VSurface() = default;
    virtual ~VSurface(void) = default;

    VkSurfaceKHR surf() const { return m_surface; }
    
    VSurface& hwnd(HWND hwnd);

    VSurface& build(VkInstance instance);

private:
    
    VkSurfaceKHR m_surface;

    VkWin32SurfaceCreateInfoKHR m_createInfo;

    HWND m_hwnd;

};

} // namespace ogun

#endif // VSurface_h