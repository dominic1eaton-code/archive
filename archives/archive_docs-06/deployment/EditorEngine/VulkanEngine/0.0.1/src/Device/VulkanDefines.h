/**
 * @brief   vulkan engine global defines 
 * @author  eatondo
 * @note    requires C++17
 */
#pragma once

/* Windows */
#ifdef RENGINE_EXPORT
#   define RENGINE_API __declspec(dllexport)
#else
#   define RENGINE_API __declspec(dllimport)
#endif

#define RENGINE_ATTR
#define RENGINE_CALL __cdecl
#define RENGINE_PTR RENGINE_CALL
#define VK_USE_PLATFORM_WIN32_KHR

/* Vulkan */
#include <stdlib.h>
#include <stdio.h>
#define VK_USE_PLATFORM_WIN32_KHR
#include <vulkan/vulkan.h>
#define GLFW_INCLUDE_VULKAN
