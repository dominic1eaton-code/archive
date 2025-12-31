/**
 * @copyright DEFAULT
 * @brief: Logical Device wrapper class
 * @note : N/A
 */
#pragma once

#include <vector>


#ifndef LOGICALDEVICE_H
#define LOGICALDEVICE_H

namespace VulkanEngine
{
    class Logger;
    class VkInstance;
    class VkSurface;
    class PhysicalDevice;

    /*
     * Logical Device wrapper class
     */
    // class VKENGINE_API LogicalDevice
    class LogicalDevice
    {
    public:
        LogicalDevice();
        virtual ~LogicalDevice(void);
        
        /* Create logical device */
        bool create(VkInstance instance, PhysicalDevice* device);

    private:
        /* Internal vulkan instance reference */
        VkInstance m_instance;
    
        /* Logging unit */
        LoggingTool::Logger* m_logger;
    };
} // VulkanEngine

#endif // LOGICALDEVICE_H