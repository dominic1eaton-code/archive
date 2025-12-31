/**
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HWindow_h
#define HWindow_h
#include <string>
#include "hstructures.h"
#include "hbasewindow.h"

namespace hesabu
{

class HWindowWin32 : public HBaseWindowWin32<HWindowWin32>
{
public:
    HWindowWin32();
    ~HWindowWin32() = default;

    /**
     * handle window event
     */
    void handleEvent();
    
    /**
     * get window status
     * @return current status of window
     */
    uint8_t status()  const { return m_status; }
    
    /**
     * handle window message
     * @param uMsg
     * @param wParam
     * @param lParam
     */
    LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam);
};

};

#endif // HWindow_h