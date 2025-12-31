/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HEvent_h
#define HEvent_h

#include <vector>

namespace ogun
{

template<class U>
class HHEvent
{
public:
    HEvent();
    virtual ~HEvent(void) = default;
    
    HEvent& build();

private:

};

} // namespace ogun

#endif // HEvent_h