/**
 * @copyright DEFAULT
 * @brief: Physical Device wrapper class
 * @note : N/A
 */
#pragma once

#include <vector>


#ifndef PHYSICALDEVICE_H
#define PHYSICALDEVICE_H

namespace VulkanEngine
{
    class Logger;
    class VkInstance;
    class VkSurface;

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
        void select();

        /* return number of available physical devices on machine */
        uint32_t count();

        /* return Attribute information of primary physical device */
        DeviceInfo info();

        /* return primary physical device selected */
        VkPhysicalDevice primary(); 
        
    private:
        /* Internal vulkan instance reference */
        VkInstance m_instance;

        /* List of available physical devices on machine */
        std::vector<VkPhysicalDevice> m_physicalDevices;

        /* Primary physical device selected */
        VkPhysicalDevice m_primaryPhysicalDevice;
        
        /* Count of physical devices available on machine */
        uint32_t m_physicalDevicesCount;

        /* Suitability rating of chosen physical device */
        uint32_t m_primaryDeviceRating;

        /* Attribute Info of primary physical device selected */
        DeviceInfo m_primaryDeviceInfo;

        /* Render Surface associated with primary physical device */
        VkSurface m_surface;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Select primary physical device for execution */
        bool selectPrimaryPhysicalDevice();

        /* Generate queue indices for determining physical device operation mode(s) that are supported for use */
        void createQueueIndices();

        /* Rate how suitable a given physical device */
        uint32_t rateDeviceSuitability(VkPhysicalDevice device, DeviceInfo &deviceInfo);

        /* Populate information for given physical device */
        void populateDeviceInfo(VkPhysicalDevice device, DeviceInfo &deviceInfo)
        
        /*  maximum usable multi sampling count available with given device */
        VkSampleCountFlagBits maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties);
        
        /* List of all available sample counts for a given physical device */
        const std::vector<VkSampleCountFlagBits> DEFAULT_STAGE_FLAG_BITS = {
            VK_SAMPLE_COUNT_64_BIT, VK_SAMPLE_COUNT_32_BIT,
            VK_SAMPLE_COUNT_16_BIT, VK_SAMPLE_COUNT_8_BIT,
            VK_SAMPLE_COUNT_4_BIT,  VK_SAMPLE_COUNT_2_BIT
        };
    };
} // VulkanEngine

#endif // PHYSICALDEVICE_H
