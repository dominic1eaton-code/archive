/**
 * @copyright DEFAULT
 * @brief: Physical Device wrapper class
 * @note : N/A
 */

#include "LogicalDevice.h"

using namespace VulkanEngine;

LogicalDevice::LogicalDevice()
    : m_instance(VK_NULL_HANDLE)
    , m_physicalDevice(VK_NULL_HANDLE)
{}

LogicalDevice::LogicalDevice(kInstance instance, PhysicalDevice* device)
    : m_instance(instance)
    , m_physicalDevice(device)
{
    create(instance, device);
}

LogicalDevice::~LogicalDevice() {}

bool create(VkInstance instance, PhysicalDevice* device)
{
    // Check vulkan instance has been created
    if(m_instance == VK_NULL_HANDLE)
    {
        m_logger->log("LogicalDevice", LoggingTool::LoggingLevel::CRITICAL) << "No vulkan instance found ! LogicalDevice has not been initialized" << LoggingTool::Logger::endl;
        return 0;
    }
    m_logger->log("LogicalDevice", LoggingTool::LoggingLevel::CRITICAL) << "Creating logical device" << LoggingTool::Logger::endl;

    // populate vulkan object creation info
    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.queueCreateInfoCount = queueCreateInfos.size();
    m_createInfo.pQueueCreateInfos = queueCreateInfos.data() ;
    m_createInfo.enabledLayerCount = m_instance->layers().size();
    m_createInfo.ppEnabledLayerNames = m_instance->layers().data();
    m_createInfo.enabledExtensionCount = m_instance->extensions().size();
    m_createInfo.ppEnabledExtensionNames = m_instance->extensions().data();   
    m_createInfo.pEnabledFeatures = &device->info().features;

    // create vulkan object
    m_instance->createVKObject(vkCreateDevice(device->primary(), 
                                            &m_createInfo, 
                                            nullptr,
                                            &m_logicalDevice));

    // Create device functionality support queueus
    vkGetDeviceQueue(m_logicalDevice, device->queueIndices().graphicsFamily.value(), 0, &m_queues.graphics);
    vkGetDeviceQueue(m_logicalDevice, device->queueIndices().presentFamily.value(), 0, &m_queues.present);
    vkGetDeviceQueue(m_logicalDevice, device->queueIndices().computeFamily.value(), 0, &m_queues.compute);
    vkGetDeviceQueue(m_logicalDevice, device->queueIndices().transferFamily.value(), 0, &m_queues.transfer);
}
