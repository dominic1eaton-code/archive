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

private:
    /**
     * @brief x position
     */
    float x; 

    /**
     * @brief y position
     */
    float y;    
};

} // namespace ogun

#endif // HMouse_h