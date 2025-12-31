

Vulkan::Vulkan()
{

}

Vulkan::~Vulkan()
{

}

void Vulkan::initialize()
{
    
    m_shaderManager->initialize(shaderLibraryInitMessage);
    
    if (vulkanInfoMessage != NULL)
    {
        /*  engine setup */
        m_appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
        m_appInfo.pApplicationName = vulkanInfoMessage->applicationName;
        m_appInfo.applicationVersion = VK_MAKE_VERSION(vulkanInfoMessage->version.major,
                                                       vulkanInfoMessage->version.minor,
                                                       vulkanInfoMessage->version.patch);
        m_appInfo.pEngineName = vulkanInfoMessage->EngineName;
        m_appInfo.engineVersion = VK_MAKE_VERSION(vulkanInfoMessage->version.major,
                                                  vulkanInfoMessage->version.minor,
                                                  vulkanInfoMessage->version.patch);
        m_appInfo.apiVersion = vulkanInfoMessage->apiVersion;

        /*  device setup */
        m_instance = new VInstance(m_appInfo);
        m_window = new VWindow(m_instance->instance());
        m_physicalDevice = new PhysicalDevice(m_instance->instance(), m_window->surface());
        m_logicalDevice = new LogicalDevice(m_physicalDevice->device(), 
                                            m_physicalDevice->info().features,
                                            m_physicalDevice->queueInfo(),
                                            m_physicalDevice->info().extensions);
        m_swapchain = new SwapChain(m_logicalDevice->device(), m_physicalDevice->indices(), m_window->surface(),
                                    m_physicalDevice->info());

        /* graphics setup */
        // create default graphics pipeline
        m_descriptor = new Descriptor(m_logicalDevice->device());
        m_pipelines.add(new GraphicsPipeline(m_logicalDevice->device(), defaultShaders, m_swapchain->extent(), m_swapchain->format(), m_descriptor->layout(), m_physicalDevice->info().depthFormat));
        m_swapchain->createFrameBuffers(m_pipelines.default->renderPass());

        // graphics render passess
        m_renderpasses.add(new ColorPass(m_logicalDevice->device(), m_swapchain->extent(), m_swapchain->framebuffers(), m_defaultPipeline, m_physicalDevice->info().memoryProperties, m_descriptor->sets()));
        m_descriptor->updateDescriptorSets(m_colorpass->uniformBuffers());
        m_passes.push_back(m_colorpass);

    }
    else
    {
        // no vulkan application initiailization acknolwedgement message found !
    }
}
