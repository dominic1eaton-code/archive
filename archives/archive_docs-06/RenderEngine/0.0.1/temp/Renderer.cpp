/**
 * @copyright DEFAULT
 * @brief: Renderer wrapper class
 * @note : N/A
 */

#include "Renderer.h"
#include "Logger.h"

using namespace RenderEngine;

/* initialization functions */

Renderer::Renderer()
    : m_logunit("Renderer")
    // , m_appInfo({})
{
    m_logger = new LoggingTool::Logger();
}

Renderer::~Renderer() 
{}

/* State functions */

bool Renderer::initialize()
{
    // set default application info if none passed in
    // VkApplicationInfo defaultAppInfo{};
    // defaultAppInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    // defaultAppInfo.pApplicationName = "RenderEngine";
    // defaultAppInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    // defaultAppInfo.pEngineName = "RenderEngine";
    // defaultAppInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    // defaultAppInfo.apiVersion = VK_API_VERSION_1_0;
    // m_appInfo = defaultAppInfo;
    
    // /* setup hardware components */
    // m_logger->log("initialize", LoggingTool::LoggingLevel::INFO) << "Setup renderer" << LoggingTool::Logger::endl;

    // // initialize vulkan instance
    // m_instance->initailze();

    // // initialize window and surface
    // m_window->intiialize();

    // // select primary physical device
    // m_device->select(m_instance->instance(), m_window->surface());

    // // initialize graphics object
    // m_graphics->initialize();
    // {
        // // initialize vulkan swapchain
        // m_swapchain->initialize();

        // /* setup render components */
        // // create default graphics piplines
        // m_pipelineManager->initialize();

        // // create default render passes
        // m_passManager->initialize();

        // // create vulkan command executor
        // m_command->initialize();
    // }
/* initialize */
    LoggingTool::Logger* m_logger = new LoggingTool::Logger();
    m_logger->enable();
    std::string m_logunit = "DeviceTest";

    // default application info from ENGINE
    VkApplicationInfo appInfo{};
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "RenderEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "RenderEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    /*  device setup */
    VInstance* m_instance = new VInstance(appInfo);
    VWindow* m_window = new VWindow(m_instance->instance());
    PhysicalDevice* m_physicalDevice = new PhysicalDevice(m_instance->instance(), m_window->surface());
    LogicalDevice* m_logicalDevice = new LogicalDevice(m_physicalDevice->device(), 
                                                                                   m_physicalDevice->info().features,
                                                                                   m_physicalDevice->queueInfo(),
                                                                                   m_physicalDevice->info().extensions);

    /* presentation setup */
    SwapChain* m_swapchain = new SwapChain(m_logicalDevice->device(), m_physicalDevice->indices(), m_window->surface(),
                                                                       m_physicalDevice->info().formats, m_physicalDevice->info().presentModes,
                                                                       m_physicalDevice->info().capabilities, m_window->extentPixels());

    /* graphics setup */
    // load default shaders
    fs::path shaderLibPath{"D:/dev/projects/RenderEngine/assets/shaders"};
    fs::path defaultShaderVert = shaderLibPath / "compiled" / "default.vert.spv";
    fs::path defaultShaderFrag = shaderLibPath / "compiled" / "default.frag.spv";
    Shader* defaultVert = new Shader(m_logicalDevice->device(), defaultShaderVert.string(), VK_SHADER_STAGE_VERTEX_BIT);
    Shader* defaultFrag = new Shader(m_logicalDevice->device(), defaultShaderFrag.string(), VK_SHADER_STAGE_FRAGMENT_BIT);
    std::vector<Shader*> defaultShaders;
    defaultShaders.push_back(defaultVert);
    defaultShaders.push_back(defaultFrag);

    // create default graphics pipeline
    GraphicsPipeline* defaultPipeline = new GraphicsPipeline(m_logicalDevice->device(), defaultShaders, m_swapchain->extent(),  m_swapchain->format());
    m_swapchain->createFrameBuffers(defaultPipeline->renderPass());

    /* scene setup */

    /* setup drawing */
    // vulkan command executor
    Command* m_command = new Command(m_logicalDevice->device(), m_physicalDevice->indices().graphicsFamily.value());

    // graphics render passess
    ColorPass* m_colorpass = new ColorPass(m_swapchain->extent(), m_swapchain->framebuffers(), defaultPipeline);
    std::vector<ColorPass*> defaultPasses;
    defaultPasses.push_back(m_colorpass);


    // @temp sync objects
    VkSemaphore imageAvailableSemaphore;
    VkSemaphore renderFinishedSemaphore;
    VkFence inFlightFence;
    VkSemaphoreCreateInfo semaphoreInfo{};
    semaphoreInfo.sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO;
    VkFenceCreateInfo fenceInfo{};
    fenceInfo.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
    fenceInfo.flags = VK_FENCE_CREATE_SIGNALED_BIT;
    Utilities::checkVKCreation(vkCreateSemaphore(m_logicalDevice->device(), &semaphoreInfo, nullptr, &imageAvailableSemaphore));
    Utilities::checkVKCreation(vkCreateSemaphore(m_logicalDevice->device(), &semaphoreInfo, nullptr, &renderFinishedSemaphore));
    Utilities::checkVKCreation(vkCreateFence(m_logicalDevice->device(), &fenceInfo, nullptr, &inFlightFence));

    return true;
}

bool Renderer::configure()
{
    // // read configuration files
    // ConfigFile rendererConfigFile();

    // // set default rendering pass
    // ColorPass* defaultPass = new defaultPass();
    // m_passes.append(defaultPass);
    return true;
}

bool Renderer::update()
{

    return true;
}
