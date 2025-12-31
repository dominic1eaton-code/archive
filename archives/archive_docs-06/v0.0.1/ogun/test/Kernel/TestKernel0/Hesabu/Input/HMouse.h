/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HMouse_h
#define HMouse_h

#include "HInput.h"
#include <vector>

namespace ogun
{

template<class U>
class HMouse : public HInput<HMouse>
{
public:
    HMouse();
    virtual ~HMouse(void) = default;
    
    HMouse& build();

private:

};

} // namespace ogun

#endif // HMouse_h