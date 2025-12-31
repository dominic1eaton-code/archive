/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HScreen_h
#define HScreen_h

#include "HInput.h"
#include <vector>

namespace ogun
{

template<class U>
class HScreen : public HInput<HScreen>
{
public:
    HScreen();
    virtual ~HScreen(void) = default;
    
private:

    /**
     * @brief monitor ID
     */
    uint32_t id;
    
    /**
     * @brief current window width
     */
    uint32_t m_width;

    /**
     * @brief current window height
     */
    uint32_t m_height;
};

} // namespace ogun

#endif // HScreen_h