/**
 * @header
 * @copyright
 * @brief
 * @note 
 */
#include <chrono>
#include <iostream>
#include <thread>
#include <vulkan/vulkan.h>
#include <vector>
#include <string>
// #include "Kernel.h"
// #include "KernelModel.h"
std::vector<const char*> findInVector(std::vector<std::string>& defaultSupportVector,
                                             std::vector<std::string>& availableSupportVector)
{
    // https://stackoverflow.com/questions/47683551/push-back-keeps-rewriting-all-entries-in-the-vector-to-the-item-pushed-back
    std::vector<const char*> support;

    // Check for support of default values in input array
    for (auto& defaultSupport : defaultSupportVector)
    {
        bool supportFound = false;
        for (auto& availableSupport : availableSupportVector)
        {
            if (strcmp(defaultSupport.c_str(), availableSupport.c_str()) == 0)
            {
                supportFound = true;
                support.push_back(defaultSupport.c_str());
                break;
            }
        }
    }
    return support;
}

void createvk(VkResult i_vObj)
{
    if (i_vObj != VK_SUCCESS) 
    {
        throw std::runtime_error("failed to create vulkan object !");
        // return false;
    }
    else
    {
        // std::cout << "created vulkan object " << std::endl; 
        // return true;
    }
}



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
    


void createInstance()
{
    VkApplicationInfo m_appInfo;
    m_appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    m_appInfo.pApplicationName = "RenderEngine";
    m_appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    m_appInfo.pEngineName = "RenderEngine";
    m_appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    m_appInfo.apiVersion = VK_API_VERSION_1_0;


    /* Main vulkan instance handle */
    VkInstance m_instance;
    
    /* Main vulkan instance creation info */
    VkInstanceCreateInfo m_createInfo;
    
    std::vector<std::string> m_defaultLayers;
    std::vector<VkLayerProperties> m_availableLayers;
    std::vector<const char*> m_layers;
    uint32_t m_layersCount;

    std::vector<std::string> m_defaultExtensions;
    std::vector<VkExtensionProperties> m_availableExtension;
    std::vector<const char*> m_extensions;
    uint32_t m_extensionsCount;

    vkEnumerateInstanceLayerProperties(&m_layersCount, nullptr);
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionsCount, nullptr);
    m_availableLayers.resize(m_layersCount);
    m_availableExtension.resize(m_extensionsCount);
    vkEnumerateInstanceLayerProperties(&m_layersCount, m_availableLayers.data());
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionsCount, m_availableExtension.data());

    std::vector<std::string> layers = {};
    for(auto layer : m_availableLayers)
        layers.push_back(layer.layerName);
    
    std::vector<std::string> extensions = {};
    for(auto extension : m_availableExtension)
        extensions.push_back(extension.extensionName);

     m_layers = findInVector(m_defaultLayers, layers);
     m_extensions = findInVector(m_defaultExtensions, extensions);

    m_createInfo.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0;
    m_createInfo.pApplicationInfo = &m_appInfo;
    m_createInfo.enabledExtensionCount = m_extensions.size();
    m_createInfo.ppEnabledExtensionNames = m_extensions.data();
    m_createInfo.enabledLayerCount = m_layers.size();
    m_createInfo.ppEnabledLayerNames = m_layers.data();

    createvk(vkCreateInstance(&m_createInfo,
                               nullptr,
                              &m_instance));


                              

                              
        std::vector<VkPhysicalDevice> m_physicalDevices;

        /* */
        VkPhysicalDevice m_physicalDevice;

        /* create device queue info for each unique queue family */
        std::vector<VkDeviceQueueCreateInfo> m_physicalDeviceQueueInfo;

        /* */
        uint32_t m_physicalDevicesCount;

        // Get list of all devices available on machine
        vkEnumeratePhysicalDevices(m_instance, &m_physicalDevicesCount, nullptr);
        m_physicalDevices.resize(m_physicalDevicesCount);

        // number of handles actually written to pPhysicalDevices
        vkEnumeratePhysicalDevices(m_instance, &m_physicalDevicesCount, m_physicalDevices.data());

        
    DeviceInfo deviceInfo;
    std::vector<VkExtensionProperties> availableExtension;
    uint32_t extensionsCount;

    VkPhysicalDevice device = m_physicalDevices[0];

    // query all available supported physical device extensions
    vkEnumerateDeviceExtensionProperties(device, nullptr, &extensionsCount, nullptr);
    availableExtension.resize(extensionsCount);
    vkEnumerateDeviceExtensionProperties(device, nullptr, &extensionsCount, availableExtension.data());

    // std::vector<std::string> extensions = {};
    // for(auto extension : availableExtension)
    //     extensions.push_back(extension.extensionName);
    // deviceInfo.extensions = findInVector(m_defaultExtensions, extensions);

    // queue family just describes a set of queues with identical properties
    vkGetPhysicalDeviceQueueFamilyProperties(device, &deviceInfo.queueFamilyPropertyCount, nullptr);
    deviceInfo.queueFamiliesProperties.resize(deviceInfo.queueFamilyPropertyCount);
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

    // // Get maximum usable multi sampling count available with given device
    // deviceInfo.msaaSamples = maxUsableSampleCount(deviceInfo.properties);

    // // query surface attributes and capabilities
    // vkGetPhysicalDeviceSurfaceCapabilitiesKHR(device, surface, &deviceInfo.capabilities);

    // query the supported surface formats
    // vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo.formatCount, nullptr);
    // if (deviceInfo.formatCount != 0) 
    // {
    //     deviceInfo.formats.resize(deviceInfo.formatCount);
    //     deviceInfo.formatProperties.resize(deviceInfo.formatCount);
    //     vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo.formatCount, deviceInfo.formats.data());

    //     // query format properties
    //     for (int i=0; i<deviceInfo.formats.size(); i++)
    //     {
    //         vkGetPhysicalDeviceFormatProperties(device, deviceInfo.formats[i].format, &deviceInfo.formatProperties[i]);
    //     }
    // }

    // // query the supported presentation modes 
    // vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo.presentModeCount, nullptr);
    // if (deviceInfo.presentModeCount != 0) 
    // {
    //     deviceInfo.presentModes.resize(deviceInfo.presentModeCount);
    //     vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo.presentModeCount,deviceInfo.presentModes.data());
    // }


}

void selectDevice()
{

}

void testModel()
{
    // ogun::KernelModel* model = new ogun::KernelModel();
    // model->initialize();
    // model->configure();
    // while (model->active())
    // {
    //     model->update();
    // }
    // model->pause();
    // model->reset();
    // model->shutdown();
    // delete model;


}

void testKernel()
{
    std::cout << "Running Vulkan kernel test 0 " << std::endl;
    // ogun::Kernel* kernel = new ogun::Kernel();
    // kernel->initialize();
    // kernel->configure();
    // while (kernel->active())
    // {
    //     kernel->update();
    // }
    // kernel->pause();
    // kernel->reset();
    // kernel->shutdown();
    // delete kernel;
}

void testComponent()
{
    using namespace std::chrono;
    // using namespace date;
    // auto rate = 400ms;
    auto frequency = 60;
    auto r = float(1.0f / frequency) * 1000.0f;
    auto rate = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::duration<float>((1.0f / frequency)));
    // auto rate = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::duration<float>((1.0f / frequency)* 1000.0f));
    // auto rate = std::chrono::duration<float>((1.0f / frequency)* 1000.0f);
    auto next = steady_clock::now();
    auto prev = next - rate;
    
    std::cout << frequency << std::endl;
    std::cout << rate.count() << std::endl;
    while (true)
    {
        // do stuff
        auto now = steady_clock::now();
        std::cout << std::chrono::round<milliseconds>(now - prev).count() << '\n';
        prev = now;

        // delay until time to iterate again
        next += rate;
        std::this_thread::sleep_until(next);
    }
}

int main(int argc, char* argv[])
{
    testModel();
    testKernel();
    // testComponent();
    createInstance();
    return 0;
}

