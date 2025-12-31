/**
 * @copyright DEFAULT
 * @brief: Vulkan main running Instance interface
 * @note : N/A
 */
#pragma once
#ifndef VINSTANCE_H
#define VINSTANCE_H

#include <string>
#include <vector>
#include "VulkanDefines.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace VulkanEngine
{

class VInstance
{
public:
    VInstance();
    VInstance(VkApplicationInfo appInfo);
    virtual ~VInstance(void);

    /* Create vulkan object */
    bool create(VkApplicationInfo appInfo);

private: 
    /* Main vulkan instance handle */
    VkInstance m_instance;

    /* Is internal vulkan object created ? */
    bool m_created;

    /* Logging unit */
    std::string m_logunit;
};

} // VulkanEngine

#endif // VINSTANCE_H
