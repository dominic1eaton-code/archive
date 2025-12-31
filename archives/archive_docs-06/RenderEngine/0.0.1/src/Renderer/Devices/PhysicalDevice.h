/**
 * @copyright default
 * @brief Physical device represents a single workforce that may comprise a single 
 *        GPU along with other hardware parts that work together to help the system 
 *        accomplish the submitted jobs. On a very simple system, a physical device 
 *        can be considered to represent the physical GPU unit.
 * @note  N/A
 */
#pragma once

#ifndef PHYSICALDEVICE_H
#define PHYSICALDEVICE_H

#include <string>
#include <vector>
#include <optional>
#include "VulkanDefines.h"

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    typedef struct DeviceInfo
    {
        /* */
        VkPhysicalDeviceProperties properties;

        /* */
        VkPhysicalDeviceFeatures features;

        /* */
        VkPhysicalDeviceMemoryProperties memoryProperties;

        /* */
        std::vector<VkQueueFamilyProperties> queueFamiliesProperties;

        /* */
        uint32_t queueFamilyPropertyCount;

        /* */
        VkSampleCountFlagBits msaaSamples;

        /* */
        uint32_t formatCount;

        /* */
        uint32_t presentModeCount;

        /* */
        VkSurfaceCapabilitiesKHR capabilities;

        /* */
        std::vector<VkSurfaceFormatKHR> formats;

        /* */
        VkFormat depthFormat;

        /* */
        VkImageTiling tiling;

        /* */
        VkFormatFeatureFlags formatFeatures;
        
        /* */
        std::vector<VkFormatProperties> formatProperties;

        /* */
        std::vector<VkPresentModeKHR> presentModes;

        /* */
        VkBool32 presentSupport;

        /* */
        uint32_t rating;

        /* Extensions */
        std::vector<const char*> extensions;

        /* Extensionscount */
        uint32_t extensionsCount;
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

    class RENGINE_API PhysicalDevice
    {
    public:
        /* */
        PhysicalDevice();

        /* */
        PhysicalDevice(VkInstance instance, VkSurfaceKHR surface);

        /* */m_defaultExtensions
        virtual ~PhysicalDevice(void);

        /*  look for and select a graphics card in the 
            system that supports the features needed */
        bool select(VkInstance instance, VkSurfaceKHR surface);

        /* */
        VkPhysicalDevice device();

        /* */
        DeviceInfo info();

        /* */
        std::vector<VkDeviceQueueCreateInfo> queueInfo();

        /* */
        QueueFamilyIndices indices();

        /* */
        bool found();

    private:
        /* */
        bool choosePhysicalDevice();

        /* */
        int rateDeviceSuitability(VkPhysicalDevice device,
                                  DeviceInfo ceviceInfo,
                                  std::vector<VkDeviceQueueCreateInfo> deviceQueueInfo);

        /* */
        DeviceInfo queryDeviceInfo(VkPhysicalDevice device, VkSurfaceKHR surface);

        /* */
        std::vector<VkDeviceQueueCreateInfo> PhysicalDevice::queryDeviceQueues(
                VkPhysicalDevice device,
                VkSurfaceKHR surface,
                std::vector<VkQueueFamilyProperties> queueFamiliesProperties,
                VkBool32 presentSupport);

        /* */
        VkFormat querySupportDepthFormat(VkImageTiling tiling);

        /* */
        void createDeviceQueueIndices();

        /* */
        VkSampleCountFlagBits maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties);

        /* */
        VkPhysicalDevice m_physicalDevice;

        /* */
        DeviceInfo m_physicalDeviceInfo;

        /* create device queue info for each unique queue family */
        std::vector<VkDeviceQueueCreateInfo> m_physicalDeviceQueueInfo;

        /* */
        uint32_t m_physicalDevicesCount;

        /* */
        bool m_deviceFound;

        /* */
        const std::vector<VkSampleCountFlagBits> DEFAULT_STAGE_FLAG_BITS = {
            VK_SAMPLE_COUNT_64_BIT, VK_SAMPLE_COUNT_32_BIT,
            VK_SAMPLE_COUNT_16_BIT, VK_SAMPLE_COUNT_8_BIT,
            VK_SAMPLE_COUNT_4_BIT,  VK_SAMPLE_COUNT_2_BIT
        };

        /* */
        const std::vector<VkFormat> DEPTH_FORMAT_CANDIDATES = {
            VK_FORMAT_D32_SFLOAT, VK_FORMAT_D32_SFLOAT_S8_UINT, VK_FORMAT_D24_UNORM_S8_UINT
        };

        /* */
        VkImageTiling m_defaultTiling;

        /* */
        VkFormatFeatureFlags m_defaultFormatFeatures;
    
        /* */
        QueueFamilyIndices m_queueFamilyIndices;

        /* Extensions */
        std::vector<std::string> m_defaultExtensions;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
} // RenderEngine

#endif // PHYSICALDEVICE_H
