/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VCommand_h
#define VCommand_h

#include "VObject.h"
#include <vector>

namespace ogun
{


class VCommand : public VObject<VCommand>
{
public:
    VCommand();
    virtual ~VCommand(void) = default;
    
    VCommand& build();

private:

};

} // namespace ogun

#endif // VCommand_h