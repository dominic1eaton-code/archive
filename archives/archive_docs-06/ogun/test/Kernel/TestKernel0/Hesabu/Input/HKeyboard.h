/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HKeyboard_h
#define HKeyboard_h

#include "HInput.h"
#include <vector>

namespace ogun
{

template<class U>
class HKeyboard : public HInput<HKeyboard>
{
public:
    HKeyboard();
    virtual ~HKeyboard(void) = default;
    
    HKeyboard& build();

private:

};

} // namespace ogun

#endif // HKeyboard_h