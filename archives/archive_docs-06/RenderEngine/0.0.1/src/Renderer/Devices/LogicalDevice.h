/**
 * @brief   logical device represents the application view of the actual device.
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef LOGICALDEVICE_H
#define LOGICALDEVICE_H

#include <string>
#include <vector>
#include <optional>
#include "VulkanDefines.h"
#include "VulkanCommon.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API LogicalDevice
    {
    public:
        LogicalDevice();
        LogicalDevice(VkPhysicalDevice device, VkPhysicalDeviceFeatures features, std::vector<VkDeviceQueueCreateInfo> queuesInfo, std::vector<const char*> extensions);
        virtual ~LogicalDevice(void);

        /* */
        bool create(VkPhysicalDevice device, VkPhysicalDeviceFeatures features, std::vector<VkDeviceQueueCreateInfo> queuesInfo, std::vector<const char*> extensions);

        /* */
        VkDevice device();
        
        /* */
        VkQueue graphicsQueue();
        
        /* */
        VkQueue presentQueue();

        /* */
        VkQueue transferQueue();

    private:
        /* Read configuration file data */
        void readConfigurationData();

        /* check instance support features */
        std::vector<const char*> checkDefaultSupport(std::vector<std::string>& defaultSupportVector,
                                                     std::vector<std::string>& availableSupportVector);

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

        /*  create the graphics queue */
        VkQueue m_graphicsQueue;

        /*  create the presentation queue */
        VkQueue m_presentQueue;

        /*  create the transfer queue */
        VkQueue m_transferQueue;

        /*  create the compute queue */
        VkQueue m_computeQueue;

        /* */
        bool m_created;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // LOGICALDEVICE_H