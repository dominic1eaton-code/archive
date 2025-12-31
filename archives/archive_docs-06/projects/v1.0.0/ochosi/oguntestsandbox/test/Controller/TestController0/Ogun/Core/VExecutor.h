/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VExecutor_h
#define VExecutor_h

#include "VObject.h"
#include <vector>

namespace ogun
{

class VExecutor : public VObject<VExecutor>
{
public:
    VExecutor();

    virtual ~VExecutor(void) = default;

    void execute();

private:

};

} // namespace ogun

#endif // VExecutor_h