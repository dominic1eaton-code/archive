/**
 * @copyright DEFAULT
 * @brief: LogicalDevice wrapper class
 * @note : N/A
 */
#pragma once

#include <vulkan/vulkan.h>
#include <vector>
#include <string>
#include <optional>

#ifndef LogicalDevice_H
#define LogicalDevice_H

namespace LoggingTool
{
    class Logger;
}

namespace RenderEngine
{
    class VInstance;
    class PhysicalDevice;

    /*
     * LogicalDevice wrapper class
     */
    // class VKENGINE_API LogicalDevice
    class LogicalDevice
    {
    public:
        LogicalDevice(VInstance* instance);
        virtual ~LogicalDevice(void);

        /* create the logical device */
        bool create(VkPhysicalDevice device, VkPhysicalDeviceFeatures features, std::vector<VkDeviceQueueCreateInfo> queuesInfo);

    private:
        /*  create the graphics queue */
        VkQueue m_graphicsQueue;

        /*  create the presentation queue */
        VkQueue m_presentQueue;

        /* Reference to instance */
        VInstance* m_instance;

        /* Reference to logical device */
        VkDevice m_logicalDevice;

        /* Creation info */
        VkDeviceCreateInfo m_createInfo;

        /* creation type */
        VkStructureType m_sType;

        /* Pointer to extension structure */
        const void* m_pNext;

        /* instance creation flags */
        VkInstanceCreateFlags m_flags;

        /* Extensions TEMP */
        std::vector<const char*> m_defaultExtensions;

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

        /* get configuration defaults */
        void getConfigDefaults();
    };
} // RenderEngine

#endif // LogicalDevice_H