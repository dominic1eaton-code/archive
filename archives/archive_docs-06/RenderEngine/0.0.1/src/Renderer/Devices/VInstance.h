/**
 * @copyright DEFAULT
 * @brief: 
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

namespace RenderEngine
{
    class RENGINE_API VInstance
    {
    public:
        VInstance();
        VInstance(VkApplicationInfo appInfo);
        virtual ~VInstance(void);

        /* Create vulkan object */
        bool create();

        /* Main vulkan instance handle */
        VkInstance instance();

    private:
        /* Main vulkan instance handle */
        VkInstance m_instance;
        
        /* Main vulkan instance creation info */
        VkInstanceCreateInfo m_createInfo;

        /* application info */
        VkApplicationInfo m_appInfo;

        /* creation type */
        VkStructureType m_sType;

        /* Pointer to extension structure */
        const void* m_pNext;

        /* instance creation flags */
        VkInstanceCreateFlags m_flags;

        /* Validation layer */
        std::vector<std::string> m_defaultLayers;

        /* Validation layer */
        std::vector<VkLayerProperties> m_availableLayers;

        /* Validation layer */
        std::vector<const char*> m_layers;

        /* Validation layer count */
        uint32_t m_layersCount;

        /* Extensions */
        std::vector<std::string> m_defaultExtensions;

        /* Extensions */
        std::vector<VkExtensionProperties> m_availableExtension;
    
        /* Extensions */
        std::vector<const char*> m_extensions;

        /* Extensionscount */
        uint32_t m_extensionsCount;

        /* */
        bool m_created;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // VINSTANCE_H