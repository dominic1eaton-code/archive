/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VShaderManager_h
#define VShaderManager_h

#include "VObject.h"
#include <vector>
#include <string>
#include "VShader.h"

namespace ogun
{

class VShaderManager : public VObject<VShaderManager>
{
public:
    VShaderManager(std::string rootPath);
    virtual ~VShaderManager(void) = default;
    
    std::vector<VShader> shaders() const { return m_shaders; }

    void load(VkDevice device);

protected:
    
    void compile();

    void parse();

private:

    std::string m_root;

std::vector<VShader> m_shaders;

    std::string compiler;

};

} // namespace ogun

#endif // VShaderManager_h