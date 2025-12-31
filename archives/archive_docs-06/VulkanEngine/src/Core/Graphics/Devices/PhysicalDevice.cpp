/**
 * @copyright DEFAULT
 * @brief: Physical Device wrapper class
 * @note : N/A
 */

#include "PhysicalDevice.h"

using namespace VulkanEngine;

PhysicalDevice::PhysicalDevice()
    : m_primaryPhysicalDevice(VK_NULL_HANDLE)
    , m_physicalDevicesCount(0)
    , m_primaryDeviceRating(0)
    , m_instance(VK_NULL_HANDLE)
    , m_surface(VK_NULL_HANDLE)
{}

PhysicalDevice::~PhysicalDevice() {}

/* PUBLIC FUNCTIONS */
void PhysicalDevice::select()
{
    // Check vulkan instance has been created, and if so
    // select primary physical device and supported operation
    // modes (queue indices)
    if(m_instance == VK_NULL_HANDLE)
    {
        m_logger->log("PhysicalDevice", LoggingTool::LoggingLevel::CRITICAL) << "No vulkan instance found ! PhysicalDevice has not been initialized" << LoggingTool::Logger::endl;
    }
    else
    {
        selectPrimaryPhysicalDevice();
        createQueueIndices();
    }
}

/* PRIVATE FUNCTIONS */
bool PhysicalDevice::selectPrimaryPhysicalDevice()
{
    m_logger->log("PhysicalDevice", LoggingTool::LoggingLevel::INFO) << "Selecting physical device to use" << LoggingTool::Logger::endl;
    
    // Get list of all devices available on machine
    vkEnumeratePhysicalDevices(m_instance, &m_physicalDevicesCount, nullptr);
    std::vector<VkPhysicalDevice> m_physicalDevices(m_physicalDevicesCount);

    // number of handles actually written to pPhysicalDevices
    vkEnumeratePhysicalDevices(m_instance, &m_physicalDevicesCount, m_physicalDevices.data());

    // Pick most suitable physical device from list
    for (auto& device : m_physicalDevices) 
    {
        DeviceInfo deviceInfo;
        uint32_t latestDeviceRating = rateDeviceSuitability(device, deviceInfo);
        if(latestDeviceRating > m_primaryDeviceRating)
        {
            m_primaryPhysicalDevice = device;
            m_primaryDeviceInfo = deviceInfo;
            m_primaryDeviceRating = latestDeviceRating;
        }
    }

    // Check if suitable device was found
    if(m_primaryDeviceRating > 0)
    {
        m_logger->log("PhysicalDevice", LoggingTool::LoggingLevel::INFO) << "Selected physical device with ID: " << deviceInfo.properties.deviceID << LoggingTool::Logger::endl;
        return false;
    }
    else
    {
        // if no suitable physical device found, return false
        return false;
    }
}

void PhysicalDevice::createQueueIndices()
{
    m_logger->log("PhysicalDevice", LoggingTool::LoggingLevel::INFO) << "Populating queue family properties for physical devices" << LoggingTool::Logger::endl;
    
    // Get supported queues for primary physical device
    vkGetPhysicalDeviceQueueFamilyProperties(m_primaryPhysicalDevice, &m_queueFamilyPropertyCount, nullptr);
    m_queueFamilyProperties.resize(m_queueFamilyPropertyCount);
    vkGetPhysicalDeviceQueueFamilyProperties(m_primaryPhysicalDevice, &m_queueFamilyPropertyCount, m_queueFamilyProperties.data());
    
    // Iterate through queue indices list to find which device specific
    // operations are supported by physical device on machine e.g. graphics,
	// presentation computation and memory transfer
    uint32_t i = 0;
    for (const auto& queueFamily : m_queueFamilyProperties)
    {
        // find devices with graphics support
        if (queueFamily.queueFlags & VK_QUEUE_GRAPHICS_BIT) 
        {
            m_queueFamilyIndices.graphicsFamily = i;
            m_queueFamilyIndices.supportedQueues |= VK_QUEUE_GRAPHICS_BIT;
        }

        // Check for presentation support
        vkGetPhysicalDeviceSurfaceSupportKHR(m_physicalDevice, i, m_surface, &m_swapChainSupportDetails.presentSupport);
        if (queueFamily.queueCount > 0 && m_swapChainSupportDetails.presentSupport) 
        {
            i++;
            m_queueFamilyIndices.presentFamily = i;
            m_queueFamilyIndices.supportedQueues |= VK_QUEUE_GRAPHICS_BIT;
        }

        // Check for compute support
        if (queueFamily.queueFlags & VK_QUEUE_COMPUTE_BIT) 
        { 
            i++;
            m_queueFamilyIndices.computeFamily = i;
            m_queueFamilyIndices.supportedQueues |= VK_QUEUE_COMPUTE_BIT;
        }

        // Check for transfer support
        if (queueFamily.queueFlags & VK_QUEUE_TRANSFER_BIT) 
        {
            i++;
            m_queueFamilyIndices.transferFamily = i;
            m_queueFamilyIndices.supportedQueues |= VK_QUEUE_TRANSFER_BIT;
        }

        if(m_queueFamilyIndices.isComplete())
            break;
        i++;
    }
    m_queueFamilyIndices.renderFamily[0] = m_queueFamilyIndices.graphicsFamily.value();
    m_queueFamilyIndices.renderFamily[1] = m_queueFamilyIndices.presentFamily.value();
    m_queueFamilyIndices.renderFamilyCount = 2;
}

uint32_t PhysicalDevice::rateDeviceSuitability(VkPhysicalDevice device, DeviceInfo &deviceInfo)
{
    uint32_t deviceRating = 0;
    populateDeviceInfo(device, deviceInfo)
    return deviceRating;
}

void PhysicalDevice::populateDeviceInfo(VkPhysicalDevice device, DeviceInfo &deviceInfo)
{
    // basic device properties for suitability query, e.g. name, 
    // type and supported Vulkan version
    vkGetPhysicalDeviceProperties(device, &(deviceInfo.properties));

    // support for optional features like texture compression, 
    // 64 bit floats and multi viewport rendering (useful for VR)
    // etc...
    vkGetPhysicalDeviceFeatures(device, &(deviceInfo.features));

    // Device memory properties
    vkGetPhysicalDeviceMemoryProperties(device, &deviceInfo.memoryProperties);

    // Get maximum usable multi sampling count available with given device
    deviceInfo.msaaSamples = maxUsableSampleCount(deviceInfo.properties);
}

VkSampleCountFlagBits PhysicalDevice::maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties)
{
    // https://stackoverflow.com/questions/5004858/why-is-stdmin-failing-when-windows-h-is-included
    // bypass #define NOMINMAX macro definition
    auto counts = (std::min)(deviceProperties.limits.framebufferColorSampleCounts,
                             deviceProperties.limits.framebufferDepthSampleCounts);
    for (const auto &sampleFlag : DEFAULT_STAGE_FLAG_BITS) 
    {
        if (counts & sampleFlag)
            return sampleFlag;
    }
    return VK_SAMPLE_COUNT_1_BIT;
}