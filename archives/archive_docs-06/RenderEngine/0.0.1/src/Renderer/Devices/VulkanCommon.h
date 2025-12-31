/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#pragma once
#ifndef VULKANCOMMON_H
#define VULKANCOMMON_H

#include <iostream>
#include <string>
#include <vector>
#include <vulkan/vulkan.h>
#include "VulkanDefines.h"

namespace RenderEngine::Utilities
{
    /* */
    bool RENGINE_API checkVKCreation(VkResult i_vObj);

    /* */
    void RENGINE_API readConfigurationData();

    /* */
    std::vector<const char*> RENGINE_API checkDefaultSupport(std::vector<std::string>& defaultSupportVector,
                                                             std::vector<std::string>& availableSupportVector);

    /* */
    std::vector<char> RENGINE_API readFile(const std::string& filename);
} // VulkanEngine

#endif // VULKANCOMMON_H
