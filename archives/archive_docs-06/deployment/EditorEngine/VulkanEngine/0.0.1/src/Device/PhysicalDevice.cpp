/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */


bool PhysicalDevice::select(VkInstance instance, VkSurfaceKHR surface)
{
    // Check vulkan instance has been created, and if so
    // select primary physical device and supported operation
    // modes (queue indices)
    if(instance == VK_NULL_HANDLE || surface == VK_NULL_HANDLE)
    {
        m_logger->log(LoggingTool::LoggingLevel::CRITICAL) << "No vulkan instance or surface found, Cannot initialize physical device !" << LoggingTool::Logger::endl;
    }
    else
    {
        std::vector<VkPhysicalDevice> availablePhysicalDevices;

        // Get list of all devices available on machine
        vkEnumeratePhysicalDevices(instance, &availablePhysicalDevicesCount, nullptr);
        availablePhysicalDevices.resize(availablePhysicalDevicesCount);

        // number of handles actually written to pPhysicalDevices
        vkEnumeratePhysicalDevices(instance, &availablePhysicalDevicesCount, availablePhysicalDevices.data());
        
        // Pick most suitable physical device from list
        uint32_t maxDeviceRating = 0;
        for (auto& device : availablePhysicalDevices) 
        {
            DeviceInfo deviceInfo = queryDeviceInfo(device, surface);
            std::vector<VkDeviceQueueCreateInfo> deviceQueueInfo = queryDeviceQueues(device, surface, deviceInfo.queueFamiliesProperties, deviceInfo.presentSupport);
            deviceInfo.rating = rateDeviceSuitability(device, deviceInfo, deviceQueueInfo);

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

}

