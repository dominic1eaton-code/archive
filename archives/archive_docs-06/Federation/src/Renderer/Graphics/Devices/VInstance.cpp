/**
 * @copyright DEFAULT
 * @brief: Main VInstance class
 * @note : N/A
 */

#include "VInstance.h"
#include <iostream>
#include "Logger.h"

using namespace RenderEngine;

VInstance::VInstance(VkApplicationInfo appInfo)
    : m_instance(VK_NULL_HANDLE)
    , m_appInfo(appInfo)
    , m_createInfo({})
    , m_sType(VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_availableLayers({})
    , m_layers()
    , m_layersCount(0)
    , m_availableExtension({})
    , m_extensions({})
    , m_extensionsCount(0)
    , m_logunit("VInstance")
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    create();
}

VInstance::~VInstance() {}

VkInstance VInstance::instance()
{
    return m_instance;
}


bool VInstance::create()
{
    // get default values from configuration files
    getConfigDefaults();

    // Check instance validation layers support
    vkEnumerateInstanceLayerProperties(&m_layersCount, nullptr);
    m_availableLayers.resize(m_layersCount);
    vkEnumerateInstanceLayerProperties(&m_layersCount, m_availableLayers.data());

    // Check instance extensions support
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionsCount, nullptr);
    m_availableExtension.resize(m_extensionsCount);
    vkEnumerateInstanceExtensionProperties(nullptr, &m_extensionsCount, m_availableExtension.data());
  
    std::vector<std::string> layers = {};
    for(auto layer : m_availableLayers)
        layers.push_back(layer.layerName);
    
    std::vector<std::string> extensions = {};
    for(auto extension : m_availableExtension)
        extensions.push_back(extension.extensionName);

     m_layers = checkDefaultSupport(m_defaultLayers, layers);
     m_extensions = checkDefaultSupport(m_defaultExtensions, extensions);

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
    createVKObject(vkCreateInstance(&m_createInfo,
                                    nullptr,
                                    &m_instance));
    return true;
}

void VInstance::getConfigDefaults()
{
    // @todo read configuration file and populate data structures
    // TEMP
    m_defaultLayers = {"VK_LAYER_KHRONOS_validation"};
    m_defaultExtensions = {"VK_KHR_surface", "VK_KHR_win32_surface"};
}


std::vector<const char*> VInstance::checkDefaultSupport(std::vector<std::string>& defaultSupportVector, std::vector<std::string>& availableSupportVector)
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

/*
 * check vulkan object has been created successfully
 */
bool VInstance::createVKObject(VkResult i_vObjResult)
{
    if (i_vObjResult != VK_SUCCESS) 
    {
        m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "failed to create vulkan object !" << LoggingTool::Logger::endl;
        throw std::runtime_error("failed to create vulkan object !");
        return false;
    }
    else
    {
        m_logger->log(m_logunit, LoggingTool::LoggingLevel::INFO) << "successfully created vulkan object" << LoggingTool::Logger::endl;
        return true;
    }
}
