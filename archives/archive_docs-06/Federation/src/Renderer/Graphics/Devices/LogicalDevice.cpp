/**
 * @copyright DEFAULT
 * @brief: LogicalDevice wrapper class
 * @note : N/A
 */

#include "LogicalDevice.h"
#include "VInstance.h"
#include "PhysicalDevice.h"
#include "Logger.h"

using namespace RenderEngine;

LogicalDevice::LogicalDevice(VInstance* instance)
    : m_logunit("LogicalDevice")
    , m_instance(instance)
    , m_createInfo({})
    , m_sType(VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_presentQueue(VK_NULL_HANDLE)
    , m_graphicsQueue(VK_NULL_HANDLE)
    , m_logicalDevice(VK_NULL_HANDLE)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

LogicalDevice::~LogicalDevice() 
{
    vkDestroyDevice(m_logicalDevice, nullptr);
}

bool LogicalDevice::create(VkPhysicalDevice device, VkPhysicalDeviceFeatures features, std::vector<VkDeviceQueueCreateInfo> queuesInfo)
{
    // get default values from configuration files
    getConfigDefaults();

    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.queueCreateInfoCount = queuesInfo.size();
    m_createInfo.pQueueCreateInfos = queuesInfo.data();
    // m_createInfo.ppEnabledLayerNames = m_enabledLayerCount;          // CURRENTLY NOT IN USE
    // m_createInfo.enabledLayerCount = m_enabledLayerCount;            // CURRENTLY NOT IN USE
    m_createInfo.ppEnabledExtensionNames = m_defaultExtensions.data();  // TEMP @todo read from config file
    m_createInfo.enabledExtensionCount = m_defaultExtensions.size();    // TEMP @todo read from config file
    m_createInfo.pEnabledFeatures = &features;

    // create vulkan object
    m_instance->createVKObject(vkCreateDevice(device,
                                             &m_createInfo,
                                             nullptr,
                                             &m_logicalDevice));

    // get device queue handles
    // presentFamily index assumed to be second item in vector
    vkGetDeviceQueue(m_logicalDevice, queuesInfo[0].queueFamilyIndex, 0, &m_graphicsQueue);
    vkGetDeviceQueue(m_logicalDevice, queuesInfo[1].queueFamilyIndex, 0, &m_presentQueue);
    return true;
}


void LogicalDevice::getConfigDefaults()
{
    // @todo read configuration file and populate data structures
    // TEMP
    m_defaultExtensions = {"VK_KHR_swapchain"};
}
