
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