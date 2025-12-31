/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "PhysicalDevice.h"
#include "VulkanCommon.h"
#include "Logger.h"
#include <set>

using namespace RenderEngine;

PhysicalDevice::PhysicalDevice()
{}

PhysicalDevice::PhysicalDevice(VkInstance instance, VkSurfaceKHR surface)
    : m_physicalDevice(VK_NULL_HANDLE)
    , m_physicalDevicesCount(0u)
    , m_deviceFound(false)
    , m_defaultExtensions({"VK_KHR_swapchain"})
    , m_defaultTiling(VK_IMAGE_TILING_OPTIMAL)
    , m_defaultFormatFeatures(VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT)
    // , m_logunit("PhysicalDevice")
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    select(instance, surface);
}

PhysicalDevice::~PhysicalDevice()
{}

bool PhysicalDevice::select(VkInstance instance, VkSurfaceKHR surface)
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "selecting physical device" << LoggingTool::Logger::endl;

    // Check vulkan instance has been created, and if so
    // select primary physical device and supported operation
    // modes (queue indices)
    if(instance == VK_NULL_HANDLE)
    {
        m_logger->log(m_logunit, LoggingTool::LoggingLevel::CRITICAL) << "No vulkan instance found, Cannot initialize physical device !" << LoggingTool::Logger::endl;
    }
    else
    {
        std::vector<VkPhysicalDevice> m_physicalDevices;

        // Get list of all devices available on machine
        vkEnumeratePhysicalDevices(instance, &m_physicalDevicesCount, nullptr);
        m_physicalDevices.resize(m_physicalDevicesCount);

        // number of handles actually written to pPhysicalDevices
        vkEnumeratePhysicalDevices(instance, &m_physicalDevicesCount, m_physicalDevices.data());

        // Pick most suitable physical device from list
        uint32_t maxDeviceRating = 0;
        for (auto& device : m_physicalDevices) 
        {
            DeviceInfo deviceInfo = queryDeviceInfo(device, surface);
            std::vector<VkDeviceQueueCreateInfo> deviceQueueInfo = queryDeviceQueues(device, surface, deviceInfo.queueFamiliesProperties, deviceInfo.presentSupport);
            deviceInfo.rating = rateDeviceSuitability(device, deviceInfo, deviceQueueInfo);

            // if DEBUG
            // for (auto& q_family : m_physicalDeviceInfo.queueFamiliesProperties)
            // {
            //     m_logger->log(m_logunit, LoggingTool::LoggingLevel::DEBUG) << "Queue number: " << std::to_string(q_family.queueCount) << LoggingTool::Logger::endl;
            //     m_logger->log(m_logunit, LoggingTool::LoggingLevel::DEBUG) << "Queue flags: "  << std::to_string(q_family.queueFlags) << LoggingTool::Logger::endl;
            // }

            // set primary device
            if ((deviceInfo.rating + 1) > maxDeviceRating)
            {
                m_physicalDevice = device;
                m_physicalDeviceInfo = deviceInfo;
                m_physicalDeviceQueueInfo = deviceQueueInfo;
                if (!m_deviceFound) {m_deviceFound = true;}
                maxDeviceRating = deviceInfo.rating;
            }
        }
    }
    return m_deviceFound;
}

VkPhysicalDevice PhysicalDevice::device() const
{
    return m_physicalDevice;
}

DeviceInfo PhysicalDevice::info() const
{
    return m_physicalDeviceInfo;
}

std::vector<VkDeviceQueueCreateInfo> PhysicalDevice::queueInfo() const
{
    return m_physicalDeviceQueueInfo;
}

QueueFamilyIndices PhysicalDevice::indices() const
{
    return m_queueFamilyIndices;
}

bool PhysicalDevice::found() const
{
    return m_deviceFound;
}

int PhysicalDevice::rateDeviceSuitability(VkPhysicalDevice device,
                                          DeviceInfo ceviceInfo,
                                          std::vector<VkDeviceQueueCreateInfo> deviceQueueInfo)
{
    uint32_t rating = 1;
    return rating;
}

DeviceInfo PhysicalDevice::queryDeviceInfo(VkPhysicalDevice device, VkSurfaceKHR surface)
{
    DeviceInfo deviceInfo;
    std::vector<VkExtensionProperties> availableExtension;
    uint32_t extensionsCount;

    // query all available supported physical device extensions
    vkEnumerateDeviceExtensionProperties(device, nullptr, &extensionsCount, nullptr);
    availableExtension.resize(extensionsCount);
    vkEnumerateDeviceExtensionProperties(device, nullptr, &extensionsCount, availableExtension.data());

    std::vector<std::string> extensions = {};
    for(auto extension : availableExtension)
        extensions.push_back(extension.extensionName);
    deviceInfo.extensions = Utilities::checkDefaultSupport(m_defaultExtensions, extensions);

    // queue family just describes a set of queues with identical properties
    vkGetPhysicalDeviceQueueFamilyProperties(device, &deviceInfo.queueFamilyPropertyCount, nullptr);
    deviceInfo.queueFamiliesProperties.resize(deviceInfo.queueFamilyPropertyCount);A
    vkGetPhysicalDeviceQueueFamilyProperties(device, &deviceInfo.queueFamilyPropertyCount, deviceInfo.queueFamiliesProperties.data());

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

    // query surface attributes and capabilities
    vkGetPhysicalDeviceSurfaceCapabilitiesKHR(device, surface, &deviceInfo.capabilities);

    // query the supported surface formats
    vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo.formatCount, nullptr);
    if (deviceInfo.formatCount != 0) 
    {
        deviceInfo.formats.resize(deviceInfo.formatCount);
        deviceInfo.formatProperties.resize(deviceInfo.formatCount);
        vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo.formatCount, deviceInfo.formats.data());

        // query format properties
        for (int i=0; i<deviceInfo.formats.size(); i++)
        {
            vkGetPhysicalDeviceFormatProperties(device, deviceInfo.formats[i].format, &deviceInfo.formatProperties[i]);
        }
    }

    // query the supported depth format
    deviceInfo.formatFeatures = m_defaultFormatFeatures;
    deviceInfo.tiling = m_defaultTiling;
    for (const auto &format  : DEPTH_FORMAT_CANDIDATES) 
    {
        VkFormatProperties props;
        vkGetPhysicalDeviceFormatProperties(device, format, &props);

        if (deviceInfo.tiling == VK_IMAGE_TILING_LINEAR && (props.linearTilingFeatures & deviceInfo.formatFeatures) == deviceInfo.formatFeatures)
        {
            deviceInfo.depthFormat = format;
        } 
        else if (deviceInfo.tiling  == VK_IMAGE_TILING_OPTIMAL && (props.optimalTilingFeatures & deviceInfo.formatFeatures) == deviceInfo.formatFeatures)
        {
            deviceInfo.depthFormat = format;
        }
    }

    // query the supported presentation modes 
    vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo.presentModeCount, nullptr);
    if (deviceInfo.presentModeCount != 0) 
    {
        deviceInfo.presentModes.resize(deviceInfo.presentModeCount);
        vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo.presentModeCount,deviceInfo.presentModes.data());
    }

    return deviceInfo;
}

std::vector<VkDeviceQueueCreateInfo> PhysicalDevice::queryDeviceQueues(
        VkPhysicalDevice device,
        VkSurfaceKHR surface,
        std::vector<VkQueueFamilyProperties> queueFamiliesProperties,
        VkBool32 presentSupport)
{
    // Iterate through queue indices list to find which device specific
    // operations are supported by physical device on machine e.g. graphics,
    // presentation computation and memory transfer
    uint32_t i = 0;
    QueueFamilyIndices queueFamilyIndices;
    std::vector<VkDeviceQueueCreateInfo> queueCreateInfos;
    for (const auto& queueFamily : queueFamiliesProperties)
    {
        // find devices with graphics support
        if (queueFamily.queueFlags & VK_QUEUE_GRAPHICS_BIT) 
        {
            queueFamilyIndices.graphicsFamily = i;
            queueFamilyIndices.supportedQueues |= VK_QUEUE_GRAPHICS_BIT;
        }
        // Check for presentation support
        vkGetPhysicalDeviceSurfaceSupportKHR(device, i, surface, &presentSupport);

        if (queueFamily.queueCount > 0 && presentSupport) 
        {
            i++;
            queueFamilyIndices.presentFamily = i;
            queueFamilyIndices.supportedQueues |= VK_QUEUE_GRAPHICS_BIT;
        }

        // Check for compute support
        if (queueFamily.queueFlags & VK_QUEUE_COMPUTE_BIT) 
        { 
            i++;
            queueFamilyIndices.computeFamily = i;
            queueFamilyIndices.supportedQueues |= VK_QUEUE_COMPUTE_BIT;
        }

        // Check for transfer support
        if (queueFamily.queueFlags & VK_QUEUE_TRANSFER_BIT) 
        {
            i++;
            queueFamilyIndices.transferFamily = i;
            queueFamilyIndices.supportedQueues |= VK_QUEUE_TRANSFER_BIT;
        }

        if(queueFamilyIndices.isComplete())
            break;
        i++;
    }
    queueFamilyIndices.renderFamily[0] = queueFamilyIndices.graphicsFamily.value();
    queueFamilyIndices.renderFamily[1] = queueFamilyIndices.presentFamily.value();
    queueFamilyIndices.renderFamilyCount = 2;

    // populate queue creation info vector // TEMP
    std::set<uint32_t> uniqueQueueFamilies = {
        queueFamilyIndices.graphicsFamily.value(),
        queueFamilyIndices.presentFamily.value()
    };
    // TEMP: assign to member variable
    m_queueFamilyIndices = queueFamilyIndices;

    uint32_t queueCount = 1u;
    float queuePriority = 1.0f;
    for (uint32_t queueFamily : uniqueQueueFamilies)
    {
        VkDeviceQueueCreateInfo queueCreateInfo{};
        queueCreateInfo.sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO;
        queueCreateInfo.queueFamilyIndex = queueFamily;
        queueCreateInfo.queueCount = queueCount;
        queueCreateInfo.pQueuePriorities = &queuePriority;
        queueCreateInfos.push_back(queueCreateInfo);
    }
    return queueCreateInfos;
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
