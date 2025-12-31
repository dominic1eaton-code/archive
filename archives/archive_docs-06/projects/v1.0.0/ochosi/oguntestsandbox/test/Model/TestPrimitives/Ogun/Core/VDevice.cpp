/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VDevice.h"
#include <string>
#include <set>

using namespace ogun;

void VPhysicalDevice::select(VkInstance instance, VkSurfaceKHR surface)
{   
    m_surface = surface;
    std::vector<VkPhysicalDevice> m_physicalDevices;
    // Get list of all devices available on machine
    vkEnumeratePhysicalDevices(instance, &m_numDevices, nullptr);
    m_physicalDevices.resize(m_numDevices);

    // number of handles actually written to pPhysicalDevices
    vkEnumeratePhysicalDevices(instance, &m_numDevices, m_physicalDevices.data());

    // Pick most suitable physical device from list
    uint32_t maxDeviceRating = 0;
    for (auto& device : m_physicalDevices)
    {
        DeviceInfo info;
        std::vector<VkDeviceQueueCreateInfo> queueInfo;
        queryDeviceInfo(device, surface, &info);
        queryDeviceQueuesInfo(device, surface, info.queueFamiliesProperties, info.presentSupport, queueInfo);
        rateDeviceSuitability(&info, queueInfo);

        // set primary device
        if (info.rating > maxDeviceRating)
        {
            m_primaryDevice = device;
            m_primaryDeviceInfo = info;
            // m_primaryDeviceQueueInfo = queueInfo;
            m_primaryDeviceQueueInfo = m_queueInfo;
            if (m_deviceFound == false) {m_deviceFound = true;}
        }
    }
}

void VPhysicalDevice::rateDeviceSuitability(DeviceInfo* info, std::vector<VkDeviceQueueCreateInfo> queueInfo)
{
    info->rating = 1;
    // info->rating = (info->rating != 0) ? 0 : 1;
}

void VPhysicalDevice::queryDeviceInfo(VkPhysicalDevice device,  VkSurfaceKHR surface, DeviceInfo* deviceInfo)
{
    // query all available supported physical device extensions
    vkEnumerateDeviceExtensionProperties(device, nullptr, &m_extensionsCount, nullptr);
    m_availableExtension.resize(m_extensionsCount);
    vkEnumerateDeviceExtensionProperties(device, nullptr, &m_extensionsCount, m_availableExtension.data());
    std::vector<std::string> extensions = {};
    for(auto extension : m_availableExtension)
        extensions.push_back(extension.extensionName);
    // deviceInfo->extensions = Utilities::checkDefaultSupport(m_defaultExtensions, extensions);

    // queue family just describes a set of queues with identical properties
    vkGetPhysicalDeviceQueueFamilyProperties(device, &deviceInfo->queueFamilyPropertyCount, nullptr);
    deviceInfo->queueFamiliesProperties.resize(deviceInfo->queueFamilyPropertyCount);
    vkGetPhysicalDeviceQueueFamilyProperties(device, &deviceInfo->queueFamilyPropertyCount, deviceInfo->queueFamiliesProperties.data());

    // basic device properties for suitability query, e.g. name, 
    // type and supported Vulkan version
    vkGetPhysicalDeviceProperties(device, &(deviceInfo->properties));

    // support for optional features like texture compression, 
    // 64 bit floats and multi viewport rendering (useful for VR)
    vkGetPhysicalDeviceFeatures(device, &(deviceInfo->features));

    // Device memory properties
    vkGetPhysicalDeviceMemoryProperties(device, &deviceInfo->memoryProperties);

    // Get maximum usable multi sampling count available with given device
    deviceInfo->msaaSamples = maxUsableSampleCount(deviceInfo->properties);

    // query surface attributes and capabilities
    vkGetPhysicalDeviceSurfaceCapabilitiesKHR(device, surface, &deviceInfo->capabilities);

    // query the supported surface formats
    vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo->formatCount, nullptr);
    if (deviceInfo->formatCount != 0) 
    {
        deviceInfo->formats.resize(deviceInfo->formatCount);
        deviceInfo->formatProperties.resize(deviceInfo->formatCount);
        vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo->formatCount, deviceInfo->formats.data());

        // query format properties
        for (int i=0; i<deviceInfo->formats.size(); i++)
        {
            vkGetPhysicalDeviceFormatProperties(device, deviceInfo->formats[i].format, &deviceInfo->formatProperties[i]);
        }
    }
    
    // query the supported presentation modes 
    vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo->presentModeCount, nullptr);
    if (deviceInfo->presentModeCount != 0) 
    {
        deviceInfo->presentModes.resize(deviceInfo->presentModeCount);
        vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo->presentModeCount, deviceInfo->presentModes.data());
    }

    // query the supported depth format
    // m_defaultFormatFeatures(VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT)
    // , m_defaultTiling(VK_IMAGE_TILING_OPTIMAL)
    deviceInfo->formatFeatures = VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT;
    deviceInfo->tiling = VK_IMAGE_TILING_OPTIMAL;
    for (const auto &format  : DEPTH_FORMAT_CANDIDATES) 
    {
        VkFormatProperties props;
        vkGetPhysicalDeviceFormatProperties(device, format, &props);

        if (deviceInfo->tiling == VK_IMAGE_TILING_LINEAR && (props.linearTilingFeatures & deviceInfo->formatFeatures) == deviceInfo->formatFeatures)
        {
            deviceInfo->depthFormat = format;
        } 
        else if (deviceInfo->tiling  == VK_IMAGE_TILING_OPTIMAL && (props.optimalTilingFeatures & deviceInfo->formatFeatures) == deviceInfo->formatFeatures)
        {
            deviceInfo->depthFormat = format;
        }
    }
}

void VPhysicalDevice::queryDeviceQueuesInfo(VkPhysicalDevice device,  VkSurfaceKHR surface, std::vector<VkQueueFamilyProperties> queueFamiliesProperties, VkBool32 presentSupport, std::vector<VkDeviceQueueCreateInfo>& queueInfo)
{
    // Iterate through queue indices list to find which device specific
    // operations are supported by physical device on machine e.g. graphics,
    // presentation computation and memory transfer
    uint32_t i = 0;
    QueueFamilyIndices queueFamilyIndices;
    std::vector<VkDeviceQueueCreateInfo> queueCreateInfos;
    for (const auto& queueFamily : queueFamiliesProperties)
    {
        // Check for presentation support
        vkGetPhysicalDeviceSurfaceSupportKHR(device, i, surface, &presentSupport);
        
        if (queueFamily.queueFlags & VK_QUEUE_GRAPHICS_BIT) 
        {
            queueFamilyIndices.graphics = i;
            queueFamilyIndices.supported |= VK_QUEUE_GRAPHICS_BIT;
        }
        if (queueFamily.queueCount > 0 && presentSupport) 
        {
            i++;
            queueFamilyIndices.present = i;
            queueFamilyIndices.supported |= VK_QUEUE_GRAPHICS_BIT;
        }
        if (queueFamily.queueFlags & VK_QUEUE_COMPUTE_BIT) 
        { 
            i++;
            queueFamilyIndices.compute = i;
            queueFamilyIndices.supported |= VK_QUEUE_COMPUTE_BIT;
        }
        if (queueFamily.queueFlags & VK_QUEUE_TRANSFER_BIT) 
        {
            i++;
            queueFamilyIndices.transfer = i;
            queueFamilyIndices.supported |= VK_QUEUE_TRANSFER_BIT;
        }
        if (queueFamily.queueFlags & VK_QUEUE_SPARSE_BINDING_BIT) 
        {
            i++;
            queueFamilyIndices.sparse = i;
            queueFamilyIndices.supported |= VK_QUEUE_SPARSE_BINDING_BIT;
        }
        if(queueFamilyIndices.isComplete())
            break;
        i++;
    }

    m_indices = queueFamilyIndices;

    // populate queue creation info vector // TEMP
    std::set<uint32_t> uniqueQueueFamilies = {
        queueFamilyIndices.graphics.value(),
        queueFamilyIndices.present.value(),
        queueFamilyIndices.compute.value(),
        queueFamilyIndices.transfer.value(),
        queueFamilyIndices.sparse.value(),
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
        queueCreateInfos.push_back(queueCreateInfo);
    }
    m_queueInfo = queueCreateInfos;
    queueInfo = queueCreateInfos;
}

VkSampleCountFlagBits VPhysicalDevice::maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties)
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


VLogicalDevice& VLogicalDevice::extensions(std::vector<const char*> extensions)
{
    m_extensions = extensions;
    return *this;
}

VLogicalDevice& VLogicalDevice::device(VkPhysicalDevice device)
{
    m_pdevice = device;
    return *this;
}

VLogicalDevice& VLogicalDevice::queueInfo(std::vector<VkDeviceQueueCreateInfo> queueInfo)
{
    m_queueInfo = queueInfo;
    return *this;
}

VLogicalDevice& VLogicalDevice::features(VkPhysicalDeviceFeatures features)
{
    m_features = features;
    return *this;
}

VLogicalDevice& VLogicalDevice::build(VkInstance instance)
{
    
    // VkPhysicalDeviceVulkan11Features features11 = {};
    // VkPhysicalDeviceFeatures2 physical_features2 = {};
    // physical_features2.pNext = &features11;
    VkPhysicalDeviceFeatures2 supported_features{};
    VkPhysicalDeviceVulkan11Features extra_features{};
    supported_features.sType = VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_FEATURES_2;
    supported_features.pNext = &extra_features;
    vkGetPhysicalDeviceFeatures2(m_pdevice, &supported_features);

    // @todo figure out queue priority data not being set in physical device class
    float priority = 1.0f;
    for (int i = 0 ; i < m_queueInfo.size(); i++)
    {
        m_queueInfo[i].pQueuePriorities = &priority;
    }
    
    m_createInfo.sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0;
    m_createInfo.queueCreateInfoCount = m_queueInfo.size();
    m_createInfo.pQueueCreateInfos = m_queueInfo.data();
    m_createInfo.ppEnabledLayerNames = NULL;
    m_createInfo.enabledLayerCount = 0;
    m_createInfo.ppEnabledExtensionNames = m_extensions.data();
    m_createInfo.enabledExtensionCount = m_extensions.size();
    m_createInfo.pEnabledFeatures = NULL;
    m_createInfo.pEnabledFeatures = &m_features;

    createvk(vkCreateDevice(m_pdevice,
                            &m_createInfo,
                            nullptr,
                            &m_device));

    m_queues.resize(m_queueInfo.size());
    uint32_t qindex = 0;
    for (auto queueInfo : m_queueInfo)
    {
        vkGetDeviceQueue(m_device, queueInfo.queueFamilyIndex, qindex, &m_queues[queueInfo.queueFamilyIndex]);
        // vkGetDeviceQueue(m_logicalDevice, queuesInfo[0].queueFamilyIndex, 0, &m_graphicsQueue);
    }

    return *this;
}
