/**
 * @file
 * @brief
 * @author
 * @note
 */

#include "VInstance.h"

using namespace VulkanEngine;

VInstance::VInstance(VkApplicationInfo* appInfo)
    : m_parameters(NULL)
{
    m_logger(m_parameters->logEnabled);
    m_debugger(m_parameters->debugEnabled);
    
    // create vulkan object
    m_createInfo.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = NULL;
    m_createInfo.pApplicationInfo = appInfo;
    m_createInfo.enabledExtensionCount = m_defaultExtensions.size();
    m_createInfo.ppEnabledExtensionNames = m_defaultExtensions.data();
    m_createInfo.enabledLayerCount = m_validator->layers().size();
    m_createInfo.ppEnabledLayerNames = m_defaultLayers.data(); 
    VulkanUtil::checkVKCreation(vkCreateInstance(&m_createInfo, 
                                                nullptr, 
                                                &m_instance),
                                                m_logger);
}