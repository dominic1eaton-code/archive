/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VDevice_h
#define VDevice_h

#include "VObject.h"
#include <Vector>
#include <optional>

namespace ogun
{
    typedef struct QueueFamilyIndices
    {
        std::optional<uint32_t> graphics;

        std::optional<uint32_t> present;
        
        std::optional<uint32_t> compute;
        
        std::optional<uint32_t> transfer;
    
        std::optional<uint32_t> sparse;

        VkQueueFlags supported = {};

        // generic self check that device has full capabilities
        bool isComplete()
        {
            return graphics.has_value() &&
                   present.has_value() &&
                   compute.has_value() &&
                   transfer.has_value() &&
                   sparse.has_value();
        }
    } QueueFamilyIndices;


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
    
class VPhysicalDevice
{
public:
    VPhysicalDevice() = default;
    virtual ~VPhysicalDevice(void) = default;

    void select(VkInstance instance, VkSurfaceKHR surface);

    VkPhysicalDevice primary() const { return m_primaryDevice; }

    DeviceInfo info() const { return m_primaryDeviceInfo; }

    std::vector<VkDeviceQueueCreateInfo> queueInfo() const { return m_primaryDeviceQueueInfo; }

    QueueFamilyIndices indices() const { return m_indices; }

protected:

    void queryDeviceInfo(VkPhysicalDevice device, VkSurfaceKHR surface, DeviceInfo* deviceInfo);

    void queryDeviceQueuesInfo(VkPhysicalDevice device,  VkSurfaceKHR surface, std::vector<VkQueueFamilyProperties> queueFamiliesProperties, VkBool32 presentSupport, std::vector<VkDeviceQueueCreateInfo>& queueInfo);

    VkSampleCountFlagBits maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties);

    void rateDeviceSuitability(DeviceInfo* info, std::vector<VkDeviceQueueCreateInfo> queueInfo);

private:

    std::vector<VkDeviceQueueCreateInfo> m_queueInfo;

    std::vector<VkExtensionProperties> m_availableExtension;

    uint32_t m_extensionsCount;

    QueueFamilyIndices m_indices;

    uint32_t m_numDevices;

    // /* primary physical device */
    // VkPhysicalDevice m_device;

    VkPhysicalDevice m_primaryDevice;

    DeviceInfo m_primaryDeviceInfo;

    std::vector<VkDeviceQueueCreateInfo> m_primaryDeviceQueueInfo;
    
    // m_physicalDevices;

    bool m_deviceFound = false;
    
    std::vector<VkDeviceQueueCreateInfo> m_physicalDeviceQueueInfo;

    const std::vector<VkSampleCountFlagBits> DEFAULT_STAGE_FLAG_BITS = {
        VK_SAMPLE_COUNT_64_BIT, VK_SAMPLE_COUNT_32_BIT,
        VK_SAMPLE_COUNT_16_BIT, VK_SAMPLE_COUNT_8_BIT,
        VK_SAMPLE_COUNT_4_BIT,  VK_SAMPLE_COUNT_2_BIT
    };

    const std::vector<VkFormat> DEPTH_FORMAT_CANDIDATES = {
        VK_FORMAT_D32_SFLOAT, VK_FORMAT_D32_SFLOAT_S8_UINT, VK_FORMAT_D24_UNORM_S8_UINT
    };

    /* */
    VkImageTiling m_defaultTiling;

    /* */
    VkFormatFeatureFlags m_defaultFormatFeatures;

};

enum class VQueueType
{
    GRAPHICS = 0,
    PRESENT,
    COMPUTE,
    TRANSFER,
    SPARSE
};

class VLogicalDevice : public VObject<VLogicalDevice>
{
public:
    VLogicalDevice() = default;
    virtual ~VLogicalDevice(void) = default;

    VkDevice primary() const { return m_device; }

    VLogicalDevice& extensions(std::vector<const char*> extensions);

    VLogicalDevice& device(VkPhysicalDevice device);

    VLogicalDevice& features(VkPhysicalDeviceFeatures features);

    VLogicalDevice& queueInfo(std::vector<VkDeviceQueueCreateInfo> queueInfo);
    
    VLogicalDevice& build(VkInstance instance);

    std::vector<VkQueue> queues() const { return m_queues; }

private:
    
    /* primary logical device */
    VkDevice m_device;
    
    VkDeviceCreateInfo m_createInfo;

    std::vector<const char*> m_extensions;

    VkPhysicalDevice m_pdevice;

    VkPhysicalDeviceFeatures m_features;

    std::vector<VkDeviceQueueCreateInfo> m_queueInfo;

    std::vector<VkQueue> m_queues;
};

class VDevice : public VObject<VDevice>
{
public:
    VDevice() = default;
    virtual ~VDevice(void) = default;

private:

    VPhysicalDevice m_pdevice;

    VLogicalDevice m_ldevice;

};

} // namespace ogun

#endif // VDevice_h