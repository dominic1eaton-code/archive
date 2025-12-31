/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VDefaultPass_h
#define VDefaultPass_h

#include "VObject.h"
#include <vector>

namespace ogun
{

class VDefaultPass : public VObject<VDefaultPass>
{
public:
    VDefaultPass();

    virtual ~VDefaultPass(void) = default;

    void execute();

private:

};

} // namespace ogun

#endif // VDefaultPass_h