/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "HWindow.h"
#include <iostream>

using namespace hesabu;

LRESULT HWindow::HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    switch (uMsg)
    {
      case WM_KEYDOWN: 
        switch (wParam)
        { 
            case VK_LEFT: 
                std::cout << "left key down " << std::endl;
                break; 

            case VK_RIGHT: 
                std::cout << "right key down " << std::endl;
                break; 

            case VK_UP: 
                std::cout << "up key down " << std::endl;
                break; 

            case VK_DOWN: 
                std::cout << "down key down " << std::endl;
                break; 

            case VK_HOME: 
                // Process the HOME key. 
                break; 

            case VK_END: 
                // Process the END key. 
                break; 

            case VK_INSERT: 
                // Process the INS key. 
                break; 

            case VK_DELETE: 
                // Process the DEL key. 
                break; 

            case VK_F2: 
                // Process the F2 key. 
                break; 

            default: 
                // Process other non-character keystrokes. 
                break; 
        }
    default:
        break;
        // return DefWindowProc(m_hwnd, uMsg, wParam, lParam);
    }

    switch (uMsg)
    {
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    case WM_SIZE:
    {
        uint32_t width = LOWORD(lParam);  // Macro to get the low-order word.
        uint32_t height = HIWORD(lParam); // Macro to get the high-order word.

        // Respond to the message:
        handleSize((UINT)wParam, width, height);
    }
        // Respond to the message:
        // handleSize(hwnd, (UINT)wParam, width, height);
        // std::cout << "window resized" << std::endl;
        // freq = (int) wParam;
        // // std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
        // switch(freq)
        // {
        //     case SIZE_RESTORED:
        //         std::cout << "w restored" << std::endl;
        //     case SIZE_MINIMIZED:
        //         std::cout << "w minimized" << std::endl;
        //     case SIZE_MAXIMIZED:
        //         std::cout << " maximized" << std::endl;
        //     case SIZE_MAXSHOW:
        //         std::cout << " show" << std::endl;
        //     case SIZE_MAXHIDE:
        //         std::cout << " hide" << std::endl;
        //     default:
        //         break;
        // }
    // case WM_CREATE:
    //     std::cout << "window created" << std::endl;
    //     std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
    // case WM_MOVE:
    //     std::cout << "window moved " << std::endl;
    //     std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
    // case WM_CLOSE:
    //     std::cout << "window closed" << std::endl;
    //     PostQuitMessage(0);
    //     return 0;
    // case WM_SHOWWINDOW:
    //     std::cout << "window show" << std::endl;
    //     std::cout << "wParam : lParam -" << wParam << " : " << lParam << std::endl;
    // case WM_MOUSEHOVER:
    //     std::cout << " window hover " << std::endl;
    case WM_PAINT:
        {
            PAINTSTRUCT ps;
            HDC hdc = BeginPaint(m_hwnd, &ps);
            FillRect(hdc, &ps.rcPaint, (HBRUSH) (COLOR_WINDOW+1));
            EndPaint(m_hwnd, &ps);
        }
        return 0;
    default:
        return DefWindowProc(m_hwnd, uMsg, wParam, lParam);
    }
    return TRUE;
}


void HWindow::handleSize(UINT flag, int width, int height)
{
    std::cout << "window resized : w - h " << width << " - " << height << std::endl;
    // std::cout << " resized flag " << flag << std::endl;
    if (flag == SIZE_RESTORED)
    {
        std::cout << "restored" << std::endl;
    }
    else if (flag == SIZE_MINIMIZED)
    {
        std::cout << "minimized" << std::endl;
    }
    else if (flag == SIZE_MAXIMIZED)
    {
        std::cout << "maximized" << std::endl;
    }
    else if (flag == SIZE_MAXSHOW)
    {
        std::cout << "show" << std::endl;
    }
    else if (flag == SIZE_MAXHIDE)
    {
        std::cout << "hide" << std::endl;
    }
    else {}
}
