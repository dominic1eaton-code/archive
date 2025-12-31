/**
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HWindow_h
#define HWindow_h

#include "HBaseWindow.h"

namespace hesabu
{


// class HWindowUnix : public HBaseWindowUnix
// {
// public:
//     HWindowUnix() = default;
//     virtual ~HWindowUnix() = default;

// };


class HWindowWin32 : public HBaseWindowWin32<HWindowWin32>
{
public:
    HWindowWin32() = default;
    virtual ~HWindowWin32() = default;

    /**
     * handle window message
     * @param uMsg
     * @param wParam
     * @param lParam
     */
    LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam) override;

    /**
     * handle key event
     */
    void handleKeyEvent();

    /**
     * handle cursor event
     */
    void handleCursorEvent();

    /**
     * handle mouse event
     */
    void handleMouseEvent();

    /**
     * handle scroll event
     */
    void handleScrollEvent() ;

    /**
     * handle screen event
     */
    void handleScreenEvent();
};

};

#endif // HWindow_h