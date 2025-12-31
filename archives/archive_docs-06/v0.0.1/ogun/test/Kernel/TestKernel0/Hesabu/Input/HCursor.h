/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HCursor_h
#define HCursor_h

#include "HInput.h"
#include <vector>

namespace ogun
{

template<class U>
class HCursor : public HInput<HCursor>
{
public:
    HCursor();
    virtual ~HCursor(void) = default;
    
    HCursor& build();

private:

};

} // namespace ogun

#endif // HCursor_h