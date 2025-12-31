/**
 * @copyright DEFAULT
 * @brief: Physical Device wrapper class
 * @note : N/A
 */

#include "PhysicalDevice.h"
#include "Logger.h"
#include <set>

using namespace RenderEngine;

PhysicalDevice::PhysicalDevice()
    : m_physicalDevicesCount(0)
    , m_physicalDevices({})
    , m_logunit("PhysicalDevice")
    , m_primaryDeviceRating(0)
    , m_primaryDeviceInfo()
    , m_primaryPhysicalDevice(VK_NULL_HANDLE)
    , m_queueFamilyPropertyCount(0)
    , m_queueFamilyProperties({})
    , m_presentSupport(false)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

PhysicalDevice::~PhysicalDevice() {}

/* PUBLIC FUNCTIONS */
void PhysicalDevice::select(VkInstance instance, VkSurfaceKHR surface)
{
    // Check vulkan instance has been created, and if so
    // select primary physical device and supported operation
    // modes (queue indices)
    if(instance == VK_NULL_HANDLE)
    {
        m_logger->log(m_logunit, LoggingTool::LoggingLevel::CRITICAL) << "No vulkan instance found, Cannot initialize !" << LoggingTool::Logger::endl;
    }
    else
    {
        selectPrimaryPhysicalDevice(instance);
        createQueueIndices(surface);
    }
}

VkPhysicalDevice PhysicalDevice::primary()
{
    return m_primaryPhysicalDevice;
}


VkPhysicalDeviceFeatures PhysicalDevice::features()
{
    return m_primaryDeviceInfo.features;
}

std::vector<VkDeviceQueueCreateInfo> PhysicalDevice::queuesInfo()
{
    return m_queueCreateInfos;
}

/* PRIVATE FUNCTIONS */
bool PhysicalDevice::selectPrimaryPhysicalDevice(VkInstance instance)
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Selecting physical device to use" << LoggingTool::Logger::endl;
    
    // Get list of all devices available on machine
    vkEnumeratePhysicalDevices(instance, &m_physicalDevicesCount, nullptr);
    m_physicalDevices.resize(m_physicalDevicesCount);

    // number of handles actually written to pPhysicalDevices
    vkEnumeratePhysicalDevices(instance, &m_physicalDevicesCount, m_physicalDevices.data());

    // Pick most suitable physical device from list
    for (auto& device : m_physicalDevices) 
    {
        DeviceInfo deviceInfo;
        uint32_t latestDeviceRating = rateDeviceSuitability(device, deviceInfo);
        if(latestDeviceRating >= m_primaryDeviceRating)
        {
            m_primaryPhysicalDevice = device;
            m_primaryDeviceInfo = deviceInfo;
            m_primaryDeviceRating = latestDeviceRating;
        }
    }

    // Check if suitable device was found
    if(m_primaryPhysicalDevice != VK_NULL_HANDLE)
    {
        // surface->querySwapchainSupport(m_primaryPhysicalDevice);
        m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Selected physical device with ID: " << m_primaryDeviceInfo.properties.deviceID << LoggingTool::Logger::endl;
        return true;
    }
    else
    {
        // if no suitable physical device found, return false
        m_logger->log(m_logunit, LoggingTool::LoggingLevel::CRITICAL) << "no suitable physical device found" << LoggingTool::Logger::endl;
        return false;
    }
}

void PhysicalDevice::createQueueIndices(VkSurfaceKHR surface)
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Populating queue index family properties for physical devices" << LoggingTool::Logger::endl;
       
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
        vkGetPhysicalDeviceSurfaceSupportKHR(m_primaryPhysicalDevice, i, surface, &m_presentSupport);
        if (queueFamily.queueCount > 0 && m_presentSupport) 
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

    // populate queue creation info vector
    // TEMP
    std::set<uint32_t> uniqueQueueFamilies = {
        m_queueFamilyIndices.graphicsFamily.value(),
        m_queueFamilyIndices.presentFamily.value()
    };

    uint32_t queueCount = 1u;
    float queuePriority = 1.0f;
    for (uint32_t queueFamily : uniqueQueueFamilies)
    {
        VkDeviceQueueCreateInfo queueCreateInfo{};
        queueCreateInfo.sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO;
        queueCreateInfo.queueFamilyIndex = queueFamily;
        queueCreateInfo.queueCount = queueCount;
        queueCreateInfo.pQueuePriorities = &queuePriority;
        m_queueCreateInfos.push_back(queueCreateInfo);
    }
}

uint32_t PhysicalDevice::rateDeviceSuitability(VkPhysicalDevice device, DeviceInfo &deviceInfo)
{
    uint32_t deviceRating = 0;
    populateDeviceInfo(device, deviceInfo);

    // @todo check swapchain supported on device
    // bool swapChainAdequate = false;
    // if (extensionsSupported) {
    //     SwapChainSupportDetails swapChainSupport = surface->querySwapChainSupport(device);
    //     swapChainAdequate = !surface->formats.empty() && !surface->presentModes.empty();
    // }

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