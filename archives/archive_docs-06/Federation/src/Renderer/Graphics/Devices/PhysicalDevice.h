/**
 * @copyright DEFAULT
 * @brief: Physical Device wrapper class
 * @note : N/A
 */
#pragma once

#include <vulkan/vulkan.h>
#include <vector>
#include <string>
#include <optional>

#ifndef PHYSICALDEVICE_H
#define PHYSICALDEVICE_H

namespace LoggingTool
{
    class Logger;
}

namespace RenderEngine
{
    class VInstance;

    /* physical device info struct */
    typedef struct DeviceInfo 
    {
        VkPhysicalDeviceProperties properties;
        VkPhysicalDeviceFeatures features;
        VkPhysicalDeviceMemoryProperties memoryProperties;
        std::vector<VkQueueFamilyProperties> queueFamiliesProperties;
        VkSampleCountFlagBits msaaSamples;
    } DeviceInfo;

    // device bit indexes to determine capabilities
    typedef struct QueueFamilyIndices
    {
        // check that a device can render graphics
        std::optional<uint32_t> graphicsFamily;

        // check that a device can present images
        // to the surface we created
        std::optional<uint32_t> presentFamily;

        // check device can perform computations 
        std::optional<uint32_t> computeFamily;

        // check device can tranfser data 
        std::optional<uint32_t> transferFamily;

        // list of queue families device can support
        VkQueueFlags supportedQueues = {};

        // render queue family indices (graphics+present queue indices)
        uint32_t renderFamily[2];
        uint32_t renderFamilyCount;

        // check device has render capabilities (can process graphics
        // and can present to screen)
        bool isRenderCapable()
        {
            return graphicsFamily.has_value() &&
                   presentFamily.has_value();
        }

        // generic self check that device has full capabilities
        bool isComplete()
        {
            return graphicsFamily.has_value() &&
                   presentFamily.has_value() &&
                   computeFamily.has_value() &&
                   transferFamily.has_value();
        }
    } QueueFamilyIndices;

    /*
     * Physical Device wrapper class
     */
    // class VKENGINE_API PhysicalDevice
    class PhysicalDevice
    {
    public:
        PhysicalDevice();
        virtual ~PhysicalDevice(void);

        /* select primary physical device to use for execution */
        void select(VkInstance instance, VkSurfaceKHR surface);

        /* Get primary physical device */
        VkPhysicalDevice primary();

        /* devices features */
        VkPhysicalDeviceFeatures features();

        /* Device creation queues info */
        std::vector<VkDeviceQueueCreateInfo> queuesInfo();

    private:
        /* Count of physical devices available on machine */
        uint32_t m_physicalDevicesCount;

        /* List of physical devices available on machine */
        std::vector<VkPhysicalDevice> m_physicalDevices;
        
        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;

        /* Suitability rating of chosen physical device */
        uint32_t m_primaryDeviceRating;
      
        /* Attribute Info of primary physical device selected */
        DeviceInfo m_primaryDeviceInfo;

        /* Primary physical device selected */
        VkPhysicalDevice m_primaryPhysicalDevice;

        /* Queue family count */
        uint32_t m_queueFamilyPropertyCount;

        /* Queue family properties list */
        std::vector<VkQueueFamilyProperties> m_queueFamilyProperties;

        /* Queue family list */
        QueueFamilyIndices m_queueFamilyIndices;

        /* Presentation to screen support available on machine */
        VkBool32 m_presentSupport;

        /* create device queue info for each unique queue family */
        std::vector<VkDeviceQueueCreateInfo> m_queueCreateInfos;

        /* Select primary physical device for execution */
        bool selectPrimaryPhysicalDevice(VkInstance instance);

        /* Generate queue indices for determining physical device operation mode(s) that are supported for use */
        void createQueueIndices(VkSurfaceKHR surface);

        /* Rate suitability of given devices */
        uint32_t rateDeviceSuitability(VkPhysicalDevice device, DeviceInfo &deviceInfo);

        /* Population info for physical device */
        void populateDeviceInfo(VkPhysicalDevice device, DeviceInfo &deviceInfo);

        /* Get maximum sub sampling count */
        VkSampleCountFlagBits maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties);

        /* Multi sampling Anti aliasing sample count flags */
        const std::vector<VkSampleCountFlagBits> DEFAULT_STAGE_FLAG_BITS = {
            VK_SAMPLE_COUNT_64_BIT, VK_SAMPLE_COUNT_32_BIT,
            VK_SAMPLE_COUNT_16_BIT, VK_SAMPLE_COUNT_8_BIT,
            VK_SAMPLE_COUNT_4_BIT,  VK_SAMPLE_COUNT_2_BIT
        };
    };
} // RenderEngine

#endif // PHYSICALDEVICE_H