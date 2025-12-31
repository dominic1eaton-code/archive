/**
 * @copyright
 * @brief
 * @note
 */

#include "hesabu/core/window/hwindow.h"
#include <iostream>
namespace hesabu
{

HWindowWin32::HWindowWin32()
: HBaseWindowWin32()
{}

void HWindowWin32::handleEvent()
{
    std::cout << "handle events" << std::endl;
}

LRESULT HWindowWin32::HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    LRESULT result = TRUE;
    switch (uMsg)
    {
    case WM_DESTROY:
    {
        PostQuitMessage(0);
        return 0;
    }
    case WM_KEYDOWN:
    {
        // handleKeyEvent();
        break;
    }
    case WM_MOUSEMOVE:
    {
        // handleCursorEvent();
        break;
    }
    case WM_LBUTTONDOWN:
    {
        // handleMouseEvent();
        break;
    }
    case WM_RBUTTONDOWN:
    {
        // handleMouseEvent();
        break;
    }
    case WM_MBUTTONDOWN:
    {
        // handleMouseEvent();
        break;
    }
    case WM_MOUSEWHEEL:
    {
        // handleScrollEvent();
        break;
    }
    case WM_SIZE:
    {
        // handleScreenEvent();
        break;
    }
    case WM_MOVE:
    {
        // handleScreenEvent();
        break;
    }
    default:
        return DefWindowProc(hwnd(), uMsg, wParam, lParam);
    }
    return result;
}

};