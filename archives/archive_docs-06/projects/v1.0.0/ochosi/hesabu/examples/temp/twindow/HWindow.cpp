/**
 * @copyright
 * @brief
 * @note 
 */

#include "HWindow.h"

using namespace hesabu;

LRESULT HWindowWin32::HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    switch (uMsg)
    {
    case WM_DESTROY:
    {
        PostQuitMessage(0);
        return 0;
    }
    case WM_KEYDOWN:
    {
        handleKeyEvent();
        break;
    }
    case WM_MOUSEMOVE:
    {
        handleCursorEvent();
    }
    case WM_LBUTTONDOWN:
    {
        handleMouseEvent();
    }
    case WM_RBUTTONDOWN:
    {
        handleMouseEvent();
    }
    case WM_MBUTTONDOWN:
    {
        handleMouseEvent();
    }
    case WM_MOUSEWHEEL:
    {
        handleScrollEvent();
    }
    case WM_SIZE:
    {
        handleScreenEvent();
    }
    case WM_MOVE:
    {
        handleScreenEvent();
    }
    default:
        return DefWindowProc(hwnd(), uMsg, wParam, lParam);
    }
    return TRUE;
}

void HWindowWin32::handleKeyEvent()
{

}

void HWindowWin32::handleCursorEvent()
{

}

void HWindowWin32::handleMouseEvent()
{

}

void HWindowWin32::handleScrollEvent()
{

}

void HWindowWin32::handleScreenEvent()
{

}
