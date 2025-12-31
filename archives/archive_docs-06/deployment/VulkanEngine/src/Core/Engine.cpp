

void Engine::configure()
{
    // load configuration parameters and options
    loadConfiguration();

    /* setup GLFW */
    glfwInit();

    // check vulkan support for GLFW
    std::cout << '\t' << glfwVulkanSupported() << '\n';


}

void Engine::init()
{
    m_assetManager->initialize();

    m_instance = new VInstance();
    m_surface;
    m_physicalDevice();



}

void Engine::run()
{
    

}