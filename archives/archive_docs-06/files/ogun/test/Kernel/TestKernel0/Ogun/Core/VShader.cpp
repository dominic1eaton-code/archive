/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "VShader.h"
#include "VFile.h"

using namespace ogun;


VShader::VShader()
    : m_entryPoint("main")
{}
    
VShader::VShader(std::string filename)
    : m_filename(filename)
{}

VShader& VShader::stage(VkShaderStageFlagBits stage)
{
    m_stage = stage;
    return *this;
}

VShader& VShader::name(std::string filename)
{
    m_filename = filename;
    return *this;
}

VShader& VShader::device(VkDevice device)
{
    m_device = device;
    return *this;
}

VShader& VShader::build()
{
    auto shaderCode = readFile(m_filename);
    m_createInfo.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0;
    m_createInfo.codeSize = shaderCode.size();
    m_createInfo.pCode = reinterpret_cast<const uint32_t*>(shaderCode.data());

    createVk(vkCreateShaderModule(m_device,
                                 &m_createInfo,
                                 nullptr,
                                 &m_shaderModule));

    return *this;
}
