/**
 * @copyright DEFAULT
 * @brief: Physical Device wrapper class
 * @note : N/A
 */

#include "VInstance.h"

using namespace VulkanEngine;

VInstance::VInstance()
{}

VInstance::~VInstance() {}

bool VInstance::create()
{
    // Check instance validation layers support
    vkEnumerateInstanceLayerProperties(&m_layerCount, nullptr);
    m_availableLayers.resize(m_layerCount);
    vkEnumerateInstanceLayerProperties(&m_layerCount, m_availableLayers.data());
    checkDefaultSupport(m_defaultLayers, m_availableLayers, m_layers);

    // Check instance extensions support
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionCount, nullptr);
    m_availableExtension.resize(m_extensionCount);
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionCount, m_availableExtension.data());
    checkDefaultSupport(m_defaultExtension, m_defaultExtensions, m_extensions);

    // populate engine application info
    VkApplicationInfo m_pApplicationInfo{};
    m_pApplicationInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    m_pApplicationInfo.pApplicationName = m_applicationName;
    m_pApplicationInfo.applicationVersion = m_applicationVersion;
    appIm_pApplicationInfonfo.pEngineName = m_EngineName;
    m_pApplicationInfo.engineVersion = m_engineVersion;
    m_pApplicationInfo.apiVersion = m_apiVersion;

    // populate vulkan object creation info
    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.pApplicationInfo = m_pApplicationInfo;
    m_createInfo.enabledExtensionCount = m_extender->extsCount();
    m_createInfo.ppEnabledExtensionNames = m_extender->exts();
    m_createInfo.enabledExtensionCount = m_defaultExtensions.size();
    m_createInfo.ppEnabledExtensionNames = m_defaultExtensions.data();
    m_createInfo.enabledLayerCount = m_validator->layers().size();
    m_createInfo.ppEnabledLayerNames = m_defaultLayers.data();
    m_createInfo.ppEnabledLayerNames = m_validator->layers().data();
    
    // create vulkan object
    createVKObject(vkCreateInstance(&m_createInfo,
                                     nullptr,
                                     &m_instance),
                                     m_logger);
}

template<typename T>
bool VInstance::checkDefaultSupport(T defaultSupportVector, T availableSupportVector, T &support)
{
    // Check for support of default values in input array
    for (const char* defaultSupport : defaultSupportVector)
    {
        bool supportFound = false;

        for (const auto& availableLayerProps : availableSupportVector)
        {
            if (strcmp(defaultSupport, availableLayerProps.layerName) == 0)
            {
                supportFound = true;
                support.push_back(defaultSupport);
                break;
            }
        }

        if (!supportFound)
        {
            availableSupportVector.clear();
            return false;
        }
    }
    return true;
}

bool VInstance::createVKObject()
{

}
