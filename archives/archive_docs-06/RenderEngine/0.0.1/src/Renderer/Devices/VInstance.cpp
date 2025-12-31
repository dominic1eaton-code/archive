/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#include "VInstance.h"
#include "VulkanCommon.h"
#include "Logger.h"
#include <iostream>

using namespace RenderEngine;

VInstance::VInstance()
{
    create();
    // m_logger = new LoggingTool::Logger();
    // m_logger->enable();
}

VInstance::VInstance(VkApplicationInfo appInfo)
    : m_instance(VK_NULL_HANDLE)
    , m_createInfo({})
    , m_appInfo(appInfo)
    , m_sType(VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    // , m_defaultLayers({"VK_LAYER_KHRONOS_validation"})
    , m_defaultLayers({}) // disable validation error messages
    , m_availableLayers({})
    , m_layers({})
    , m_layersCount(0)
    , m_defaultExtensions({"VK_KHR_surface", "VK_KHR_win32_surface"})
    , m_availableExtension({})
    , m_extensions({})
    , m_extensionsCount(0)
    , m_created(false)
    , m_logunit("VInstance")
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    create();
}

VInstance::~VInstance()
{}

bool VInstance::create()
{
    m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "Creating vulkan instance" << LoggingTool::Logger::endl;

    // get default data
    Utilities::readConfigurationData();

    // Check instance extensions and validation layers support
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

     m_layers = Utilities::checkDefaultSupport(m_defaultLayers, layers);
     m_extensions = Utilities::checkDefaultSupport(m_defaultExtensions, extensions);

    // populate vulkan object creation info
    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.pApplicationInfo = &m_appInfo;
    m_createInfo.enabledExtensionCount = m_extensions.size();
    m_createInfo.ppEnabledExtensionNames = m_extensions.data();
    m_createInfo.enabledLayerCount = m_layers.size();
    m_createInfo.ppEnabledLayerNames = m_layers.data();

    // create vulkan object
    m_created = Utilities::checkVKCreation(vkCreateInstance(&m_createInfo,
                                                             nullptr,
                                                            &m_instance));
    return m_created; 
}

VkInstance VInstance::instance()
{
    return m_instance;
}
