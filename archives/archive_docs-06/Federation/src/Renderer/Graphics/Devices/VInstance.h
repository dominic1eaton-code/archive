/**
 * @copyright DEFAULT
 * @brief: Main VInstance class
 * @note : N/A
 * @reference:
 *  https://registry.khronos.org/vulkan/specs/1.3-extensions/man/html/VkInstanceCreateInfo.html
 */
#pragma once

#include <vulkan/vulkan.h>
#include <vector>
#include <string>

#ifndef VINSTANCE_H
#define VINSTANCE_H

namespace LoggingTool
{
    class Logger;
}
namespace RenderEngine
{

    class VInstance
    {
    public:
        VInstance(VkApplicationInfo appInfo);
        virtual ~VInstance(void);

        /* Get vulkan instance */
        VkInstance instance();

        /* check vulkan object has been created successfully */
        bool createVKObject(VkResult i_vObjResult);

    private:
        /* Vulkan object */
        VkInstance m_instance;

        /* application info */
        VkApplicationInfo m_appInfo;

        /* Creation info */
        VkInstanceCreateInfo m_createInfo;

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

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;

        /* create the instance object */
        bool create();

        /* check instance support features */
        std::vector<const char*> checkDefaultSupport(std::vector<std::string>& defaultSupportVector, std::vector<std::string>& availableSupportVector);    
       
        /* get configuration defaults */
        void getConfigDefaults();
    };
} // RenderEngine

#endif // VINSTANCE_H
