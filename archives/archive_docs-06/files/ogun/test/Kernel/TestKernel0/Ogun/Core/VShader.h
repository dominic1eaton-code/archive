/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VShader_h
#define VShader_h

#include "VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VShader : public VObject<VShader>
{
public:
    VShader();

    VShader(std::string filename);
    
    virtual ~VShader(void) = default;

    VkShaderStageFlagBits stage() const { return m_stage; }
    
    std::string entryPoint() const { return m_entryPoint; }

    VkShaderModule shader() const { return m_shaderModule; }

    VShader& name(std::string filename);

    VShader& device(VkDevice device);

    VShader& stage(VkShaderStageFlagBits stage);

    VShader& build();

private:

    /* */
    VkShaderModule m_shaderModule;

    /* */
    VkShaderModuleCreateInfo m_createInfo;

    /* */
    VkShaderStageFlagBits m_stage;

    /* */
    std::string m_entryPoint;

    /* */
    VkDevice m_device;

    /* */
    std::string  m_filename;

};

} // namespace ogun

#endif // VShader_h