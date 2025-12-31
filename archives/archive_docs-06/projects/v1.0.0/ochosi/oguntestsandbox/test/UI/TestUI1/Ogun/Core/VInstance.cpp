/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VInstance.h"

using namespace ogun;

VInstance& VInstance::info(VkApplicationInfo info)
{
    m_info = info;
    return *this;
}

VInstance& VInstance::layers(std::vector<const char*> layers)
{
    m_layers = layers;
    return *this;
}

VInstance& VInstance::extensions(std::vector<const char*> extensions)
{
    m_extensions = extensions;
    return *this;
}

VInstance& VInstance::build()
{   
    vkEnumerateInstanceLayerProperties(&m_layersCount, nullptr);
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionsCount, nullptr);
    m_availableLayers.resize(m_layersCount);
    m_availableExtension.resize(m_extensionsCount);
    vkEnumerateInstanceLayerProperties(&m_layersCount, m_availableLayers.data());
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionsCount, m_availableExtension.data());

    m_createInfo.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0;
    m_createInfo.pApplicationInfo = &m_info;
    m_createInfo.enabledExtensionCount = m_extensions.size();
    m_createInfo.ppEnabledExtensionNames = m_extensions.data();
    m_createInfo.enabledLayerCount = m_layers.size();
    m_createInfo.ppEnabledLayerNames = m_layers.data();

    createvk(vkCreateInstance(&m_createInfo,
                               nullptr,
                              &m_instance));
    return *this;
}
