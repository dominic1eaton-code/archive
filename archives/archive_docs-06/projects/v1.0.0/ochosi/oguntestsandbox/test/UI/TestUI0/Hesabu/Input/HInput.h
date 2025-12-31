/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HInput_h
#define HInput_h

#include <vector>

namespace ogun
{

template<class U>
class HHInput
{
public:
    HInput();
    virtual ~HInput(void) = default;
    
    /**
     * @brief build input object
     * @return input object
     */
    HInput& build();

private:

};

} // namespace ogun

#endif // HInput_h