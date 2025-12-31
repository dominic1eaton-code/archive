/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VIndexBuffer_h
#define VIndexBuffer_h

#include "Ogun/Core/VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VIndexBuffer : public VObject<VIndexBuffer>
{
public:
    VIndexBuffer();
    
    virtual ~VIndexBuffer(void) = default;

private:

};

} // namespace ogun

#endif // VIndexBuffer_h