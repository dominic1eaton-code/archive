/**
 * @brief   
 * @note    N/A
 */
#include "LogicalDevice.h"
#include "Logger.h"

using namespace RenderEngine;

LogicalDevice::LogicalDevice()
{}

LogicalDevice::LogicalDevice(VkPhysicalDevice device, 
                             VkPhysicalDeviceFeatures features, 
                             std::vector<VkDeviceQueueCreateInfo> queuesInfo,
                             std::vector<const char*> extensions)
    : m_logunit("LogicalDevice")
    , m_logicalDevice(VK_NULL_HANDLE)
    , m_sType(VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_presentQueue(VK_NULL_HANDLE)
    , m_graphicsQueue(VK_NULL_HANDLE)
    , m_transferQueue(VK_NULL_HANDLE)
    , m_computeQueue(VK_NULL_HANDLE)
    , m_created(false)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    create(device, features, queuesInfo, extensions);
}

LogicalDevice::~LogicalDevice()
{
    vkDestroyDevice(m_logicalDevice, nullptr);
}

bool LogicalDevice::create(VkPhysicalDevice device,
                           VkPhysicalDeviceFeatures features,
                           std::vector<VkDeviceQueueCreateInfo> queuesInfo,
                           std::vector<const char*> extensions)
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Creating logical device" << LoggingTool::Logger::endl;
    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.queueCreateInfoCount = queuesInfo.size();
    m_createInfo.pQueueCreateInfos = queuesInfo.data();
    // m_createInfo.ppEnabledLayerNames = m_enabledLayerCount; // Not in use by newer versions of vulkan
    m_createInfo.enabledLayerCount = 0;                        // Not in use by newer versions of vulkan
    m_createInfo.ppEnabledExtensionNames = extensions.data();
    m_createInfo.enabledExtensionCount = extensions.size();
    m_createInfo.pEnabledFeatures = &features;

    // create vulkan object
    m_created = Utilities::checkVKCreation(vkCreateDevice(device,
                                                         &m_createInfo,
                                                          nullptr,
                                                         &m_logicalDevice));

    // get device queue handles.
    // presentFamily index assumed to be second item in vector
    vkGetDeviceQueue(m_logicalDevice, queuesInfo[0].queueFamilyIndex, 0, &m_graphicsQueue);
    vkGetDeviceQueue(m_logicalDevice, queuesInfo[0].queueFamilyIndex, 0, &m_presentQueue);  // @temp present and graphics must be the same to be supported on this platform
    vkGetDeviceQueue(m_logicalDevice, queuesInfo[0].queueFamilyIndex, 0, &m_transferQueue); // @temp transfer and graphics must be the same to be supported on this platform
    return m_created;
}

VkDevice LogicalDevice::device()
{
    return m_logicalDevice;
}

VkQueue LogicalDevice::graphicsQueue()
{
    return m_graphicsQueue;
}

VkQueue LogicalDevice::presentQueue()
{
    return m_presentQueue;
}

VkQueue LogicalDevice::transferQueue()
{
    return m_transferQueue;
}

