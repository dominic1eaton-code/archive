/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VUniformBuffer_h
#define VUniformBuffer_h

#include "Ogun/Core/VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VUniformBuffer : public VObject<VUniformBuffer>
{
public:
    VUniformBuffer();
    
    virtual ~VUniformBuffer(void) = default;

private:

};

} // namespace ogun

#endif // VUniformBuffer_h