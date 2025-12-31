/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VInstance_h
#define VInstance_h

#include "VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VInstance : public VObject<VInstance>
{
public:
    VInstance() = default;
    virtual ~VInstance(void) = default;

    VInstance& info(VkApplicationInfo info);

    VInstance& layers(std::vector<const char*> layers);

    VInstance& extensions(std::vector<const char*> extensions);

    VInstance& build();

    VkInstance inst() const { return m_instance; }

private:

    VkInstance m_instance;

    VkInstanceCreateInfo m_createInfo;

    VkApplicationInfo m_info;

    std::vector<const char*> m_layers;

    std::vector<VkLayerProperties> m_availableLayers;

    std::vector<std::string> m_defaultLayers;

    uint32_t m_layersCount;

    std::vector<const char*> m_extensions;
    
    std::vector<VkExtensionProperties> m_availableExtension;
    
    std::vector<std::string> m_defaultExtensions;

    uint32_t m_extensionsCount;

};

} // namespace ogun

#endif // VInstance_h