/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "Shader.h"
#include "Logger.h"
#include "VulkanCommon.h"

using namespace RenderEngine;

Shader::Shader()
{}

Shader::Shader(VkDevice device, std::string shader, VkShaderStageFlagBits stage)
    : m_defaultEntryPoint("main")
    , m_shaderModule(VK_NULL_HANDLE)
    , m_device(device)
    , m_shaderName(shader)
    , m_created(false)
    , m_sType(VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO)
    , m_pNext(NULL)
    , m_flags(0)
    , m_stage(stage)
{
    m_entryPoint = m_defaultEntryPoint;
    create();
}

Shader::~Shader()
{
    vkDestroyShaderModule(m_device, m_shaderModule, nullptr);
}

const char* Shader::entryPoint()
{
    return m_entryPoint.c_str();
}

VkShaderModule Shader::shader()
{
    return m_shaderModule;
}
VkShaderStageFlagBits Shader::stage()
{
    return m_stage;
}

bool Shader::create()
{
    auto shaderCode = RenderEngine::Utilities::readFile(m_shaderName);
    m_createInfo.sType = m_sType;
    m_createInfo.pNext = m_pNext;
    m_createInfo.flags = m_flags;
    m_createInfo.codeSize = shaderCode.size();
    m_createInfo.pCode = reinterpret_cast<const uint32_t*>(shaderCode.data());

    // create vulkan object
    m_created = Utilities::checkVKCreation(vkCreateShaderModule(m_device,
                                                               &m_createInfo,
                                                                nullptr,
                                                               &m_shaderModule));
    return m_created;
}