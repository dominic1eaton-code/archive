/**
 * @file
 * @brief
 * @author
 * @note
 */

#include "Surface.h"
#include "VInstance.h"
#include "Utility/VulkanUtil.h"

using namespace VulkanEngine;

Surface::Surface()
    : m_sType(VK_STRUCTURE_TYPE_WIN32_SURFACE_CREATE_INFO_KHR)
    , m_instance(VK_NULL_HANDLE)
    , m_pNext(NULL)
    , m_flags(0)
{}

Surface::Surface(VkInstance instance, VWindow* window)
    : m_sType(VK_STRUCTURE_TYPE_WIN32_SURFACE_CREATE_INFO_KHR)
    , m_instance(instance)
    , m_pNext(NULL)
    , m_flags(0)
{
    create(instance, window)
}

Surface::~Surface()
{

}

VkSurfaceKHR Surface::create(VkInstance instance, VWindow* window)
{
    // populate vulkan object creation info
    m_createInfo.sType = m_sType;
    m_createInfo.hwnd = window->hwnd();
    m_createInfo.hinstance = window->hinstance();
    m_createInfo.flags = m_flags;
    m_createInfo.pNext = m_pNext;

    // create vulkan object
    m_instance->createVKObject(vkCreateWin32SurfaceKHR(m_instance->instance(), 
                                                     &m_createInfo, 
                                                     nullptr, 
                                                     &m_surface));
}
