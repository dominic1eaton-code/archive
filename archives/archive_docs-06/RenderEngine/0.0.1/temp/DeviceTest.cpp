/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#include <iostream>
#include <filesystem>
#include "VInstance.h"
#include "VWindow.h"
#include "PhysicalDevice.h"
#include "LogicalDevice.h"
#include "Buffer/SwapChain.h"
#include "Pipeline/GraphicsPipeline.h"
#include "Pipeline/Shader.h"
#include "Logger.h"
#include "VulkanCommon.h"
#include <vector>

namespace fs = std::filesystem;

int main(int argc, char **argv) 
{
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
    RenderEngine::VInstance* m_instance = new RenderEngine::VInstance(appInfo);
    RenderEngine::VWindow* m_window = new RenderEngine::VWindow(m_instance->instance());
    RenderEngine::PhysicalDevice* m_physicalDevice = new RenderEngine::PhysicalDevice(m_instance->instance(), m_window->surface());
    RenderEngine::LogicalDevice* m_logicalDevice = new RenderEngine::LogicalDevice(m_physicalDevice->device(), 
                                                                                   m_physicalDevice->info().features,
                                                                                   m_physicalDevice->queueInfo(),
                                                                                   m_physicalDevice->info().extensions);

    /* presentation setup */
    RenderEngine::SwapChain* m_swapchain = new RenderEngine::SwapChain(m_logicalDevice->device(), m_physicalDevice->indices(), m_window->surface(),
                                                                       m_physicalDevice->info().formats, m_physicalDevice->info().presentModes,
                                                                       m_physicalDevice->info().capabilities, m_window->extentPixels());

    /* graphics setup */
    // load default shaders
    fs::path shaderLibPath{"D:/dev/projects/RenderEngine/assets/shaders"};
    // fs::path defaultShaders {"default"};
    // fs::path pathToIndex = shaderLibPath / "default" / "default.vert";
    // std::cout << "Parent path: "      << pathToIndex.parent_path()   << std::endl
    //           << "exists() = "        << fs::exists(pathToIndex)     << std::endl
    //           << "root_name() = "     << pathToIndex.root_name()     << std::endl
    //           << "root_path() = "     << pathToIndex.root_path()     << std::endl
    //           << "relative_path() = " << pathToIndex.relative_path() << std::endl
    //           << "parent_path() = "   << pathToIndex.parent_path()   << std::endl
    //           << "filename() = "      << pathToIndex.filename()      << std::endl
    //           << "stem() = "          << pathToIndex.stem()          << std::endl
    //           << "extension() = "     << pathToIndex.extension()     << std::endl;
    // fs::path defaultShaderVert = shaderLibPath / "default" / "default.vert";
    // fs::path defaultShaderFrag = shaderLibPath / "default" / "default.frag";
    // auto shaderCode = RenderEngine::Utilities::readFile(defaultShaderVert.string());
    fs::path defaultShaderVert = shaderLibPath / "compiled" / "default.vert.spv";
    fs::path defaultShaderFrag = shaderLibPath / "compiled" / "default.frag.spv";
    RenderEngine::Shader* defaultVert = new RenderEngine::Shader(m_logicalDevice->device(), defaultShaderVert.string(), VK_SHADER_STAGE_VERTEX_BIT);
    RenderEngine::Shader* defaultFrag = new RenderEngine::Shader(m_logicalDevice->device(), defaultShaderFrag.string(), VK_SHADER_STAGE_FRAGMENT_BIT);
    std::vector<RenderEngine::Shader*> defaultShaders;
    defaultShaders.push_back(defaultVert);
    defaultShaders.push_back(defaultFrag);

    // create default graphics pipeline
    RenderEngine::GraphicsPipeline* defaultPipeline = new RenderEngine::GraphicsPipeline(m_logicalDevice->device(), defaultShaders, m_swapchain->extent(),  m_swapchain->format());

    /* Draw */
    

    return 0;
}
