/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VShaderManager.h"
#include <filesystem>

using namespace ogun;

VShaderManager::VShaderManager(std::string rootPath)
    : m_root(rootPath)
    , m_shaders({})
    , compiler("D:/global/VulkanSDK/1.3.296.0/Bin/glslc.exe")
{}


void VShaderManager::compile()
{

}

void VShaderManager::parse()
{

}

void VShaderManager::load(VkDevice device)
{
    std::vector<std::filesystem::path> shaderFiles;
    shaderFiles.push_back(std::filesystem::path(m_root) / "test" / "testShader0.vert.spv");
    shaderFiles.push_back(std::filesystem::path(m_root)  / "test" / "testShader0.frag.spv");

    VShader shader;
    shader.name(shaderFiles[0].string())
        .stage(VK_SHADER_STAGE_VERTEX_BIT)
        .device(device)
        .build();
    m_shaders.push_back(shader);

    VShader shader0;
    shader0.name(shaderFiles[1].string())
        .stage(VK_SHADER_STAGE_FRAGMENT_BIT)
        .device(device)
        .build();
    m_shaders.push_back(shader0);

    // for (auto file : shaderFiles)
    // {
    //     VShader shader;
    //     shader.name(file.string())
    //         .stage()
    //         .device(device)
    //         .build();
    //     m_shaders.push_back(shader);
    // }
}
