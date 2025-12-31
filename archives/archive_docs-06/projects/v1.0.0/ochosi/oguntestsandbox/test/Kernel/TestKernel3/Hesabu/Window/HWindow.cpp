/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "HWindow.h"
#include <iostream>
#include "vulkan_exec.h"
#include <windowsx.h>
#include <Xinput.h> // Necessary for XInput constants, even if not directly using XInput


using namespace hesabu;

HWindow::HWindow()
    : HBaseWindow("")
{
    model = new ogun::VulkanModel();
}

void HWindow::draw()
{
    if (!bInit)
    {
        init();
        bInit = true;
    }
    else
    {
        update();
    }
}

void HWindow::init()
{
    ogun::VulkanModelInfo info;
    info.window.hwnd = m_hwnd;
    info.window.name = m_name;
    info.window.height = 800;
    info.window.width = 600;
    info.mount = "D:";
    // info.shaderLibraryPath = "D:/dev/projects/ogun/assets/shaders";
    // info.shaderLibraryPath = "D:/dev/projects/v0.0.1/ogunv2/ogun/assets/shaders";
    model->init(info);
}

void HWindow::update()
{
    static auto startTime = std::chrono::high_resolution_clock::now();
    auto currentTime = std::chrono::high_resolution_clock::now();
    float tick = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();
    model->draw(tick);
}

void HWindow::pollEvent(uint32_t& e)
{
    poll();
    e = state();
}

// enum class NumberKey : unsigned int {
//     NUM_0 = 0x30, // 0 key
//     NUM_1 = 0x31, // 1 key
//     NUM_2 = 0x32, // 2 key
//     NUM_3 = 0x33, // 3 key
//     NUM_4 = 0x34, // 4 key
//     NUM_5 = 0x35, // 5 key
//     NUM_6 = 0x36, // 6 key
//     NUM_7 = 0x37, // 7 key
//     NUM_8 = 0x38, // 8 key
//     NUM_9 = 0x39  // 9 key
// };

void HWindow::handleKeyPress(WPARAM wParam)
{
    switch (wParam)
    {   
        case 0x31:
            std::cout << "object X+" << std::endl;
            model->moveObject(glm::vec3(1.0, 0.0, 0.0));
            break;
    
        case 0x32:
            std::cout << "object Y+" << std::endl;
            model->moveObject(glm::vec3(0.0, 1.0, 0.0));
            break;

        case 0x33:
            std::cout << "object X-" << std::endl;
            model->moveObject(glm::vec3(-1.0, 0.0, 0.0));
            break;

        case 0x34:
            std::cout << "object Y-" << std::endl;
            model->moveObject(glm::vec3(0.0, -1.0, 0.0));
            break;
    
        case 0x35:
            std::cout << "object Z+" << std::endl;
            model->moveObject(glm::vec3(0.0, 0.0, 1.0));
            break;

        case 0x36:
            std::cout << "object Z-" << std::endl;
            model->moveObject(glm::vec3(0.0, 0.0, -1.0));
            break;
    
        case VK_NUMPAD8:
            std::cout << "FORWARD" << std::endl;
            model->transform(1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 1);
            model->transform(1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 2);
            break;
            
        case VK_NUMPAD2:
            std::cout << "BACK" << std::endl;
            model->transform(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 1);
            model->transform(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 2);
            break;
            
        case VK_NUMPAD4:
            std::cout << "LEFT" << std::endl;
            model->transform(1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 1);
            model->transform(1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 2);
            break;
            
        case VK_NUMPAD6:
            std::cout << "RIGHT" << std::endl;
            model->transform(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 1);
            model->transform(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 2);
            break;

        case VK_UP:
            std::cout << "UP" << std::endl;
            model->transform(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1);
            model->transform(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2);
            break;
            
        case VK_DOWN:
            std::cout << "DOWN" << std::endl;
            model->transform(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1);
            model->transform(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2);
            break;

        case VK_F1:
            std::cout << "Fill polygon mode" << std::endl;
            model->rebuildPipeline(VK_POLYGON_MODE_FILL);
            break;
            
        case VK_F2:
            std::cout << "Wire frame polygon mode" << std::endl;
            model->rebuildPipeline(VK_POLYGON_MODE_LINE);
            break;
            
        case VK_F3:
            std::cout << "Point polygon mode" << std::endl;
            model->rebuildPipeline(VK_POLYGON_MODE_POINT);
            break;

        case VK_F4:
            std::cout << "Switching current active object" << std::endl;
            model->switchActiveObject();
            break;

        case 'R':
            std::cout << "Recompiling shaders..." << std::endl;
            model->recompileShaders();
            break;

        case 'W':
            model->transform(1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 0);
            break;
            
        case 'S':
            model->transform(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 0);
            break;
            
        case 'A':
            model->transform(1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 0);
            break;
            
        case 'D':
            model->transform(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 0);
            break;

        case 'Z':
            model->transform(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 0);
            break;
            
        case 'X':
            model->transform(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 0);
            break;

        case 'T':
            model->transform(1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 1);
            break;

        case 'G':
            model->transform(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 1);
            break;

        case 'F':
            model->transform(1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 1);
            break; 

        case 'H':
            model->transform(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 1);
            break; 
        
        case 'V':
            model->transform(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1);
            break; 

        case 'B':
            model->transform(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1);
            break;

        case 'I':
            model->transform(1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 2);
            break;

        case 'K':
            model->transform(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 2);
            break;

        case 'J':
            model->transform(1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 2);
            break; 

        case 'L':
            model->transform(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 2);
            break; 
        
        case 'N':
            model->transform(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2);
            break; 

        case 'M':
            model->transform(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2);
            break; 

        default: 
            // Process other non-character keystrokes. 
            break; 
    }
};

LRESULT HWindow::HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    switch (uMsg)
    {
    case WM_KEYDOWN:
        // switch(wParam)
        // {
        // case 'A':
        // {
        //     testState = 68;
        //     break;
        // }
        // case 'B':
        // {
        //     testState = 69;
        //     break;
        // }
        // case 'C':
        // {
        //     testState = 70;
        //     break;
        // }
        // default:
        //     break;
        // }
        handleKeyPress(wParam);
        // {
        //     BOOL bretk =  PostMessageA(
        //         m_hwnd,
        //         uMsg,
        //         wParam,
        //         lParam
        //       );
        // }
        // testState++;
    default:
        break;
    }

    POINT windowCursorPosition;
    POINT cursorPosition;
    RECT windowRect;
    const HWND hDesktop = GetDesktopWindow();
    RECT desktopRect;
    uint32_t xPos;
    uint32_t yPos;
    switch (uMsg)
    {
    case WM_DESTROY:
    {
        PostQuitMessage(0);
        return 0;
    }
    //**********************************************************************************/
    // case WM_LBUTTONDOWN:
    // {
    //     // GetCursorPos(&cursorPosition);
    //     uint32_t width = LOWORD(lParam);  // Macro to get the low-order word.
    //     uint32_t height = HIWORD(lParam); // Macro to get the high-order word.
    //     std::cout << "moving mouse " << "x: " << width << " : y: "<< height << std::endl;
    //     // OnMouseMove(hwnd, (UINT)wParam, cursorPosition.x, cursorPosition.y);
    //     draw();
    //     break;
    // }
    //**********************************************************************************/
    case WM_MOUSEMOVE:
    {
        GetWindowRect(m_hwnd, &windowRect);
        GetCursorPos(&cursorPosition);
        float cposx = cursorPosition.x - windowRect.left;
        float cposy = cursorPosition.y - windowRect.top;
        float cndcx = -(2*(cposx / (windowRect.left - windowRect.right)) + 1);
        float cndcy =  (2*(cposy / (windowRect.top - windowRect.bottom)) + 1);
        // std::cout << "screen cursor position " << "x: " << cposx << " : y: "<< cposy << std::endl;
        // std::cout << "NDC cursor position " << "x: " << cndcx << " : y: "<< cndcy << std::endl;
        // model->handleCursor(cursorPosition.x - windowRect.left,  cursorPosition.y - windowRect.top);
        // model->handleCursor(cndcx, cndcy);
        model->handleCursor(cposx, cposy);
        if ((DWORD)wParam & MK_LBUTTON) 
        { 
            GetWindowRect(hDesktop, &desktopRect);
            std::cout << "window rect " << " t.x: " << windowRect.left
                                        << " t.y: " << windowRect.top
                                        << " b.x: " << windowRect.right
                                        << " b.y: " << windowRect.bottom
                                        << std::endl;

            std::cout << "desktop rect " << " d.x: " << desktopRect.left
                                         << " d.y: " << desktopRect.top
                                         << " d.x: " << desktopRect.right
                                         << " d.y: " << desktopRect.bottom
                                         << std::endl;

            windowCursorPosition.x = (cursorPosition.x / desktopRect.right) * windowRect.bottom;
            float posx = (cursorPosition.x * (float(windowRect.right - windowRect.left) / desktopRect.right)) - windowRect.left;
            windowCursorPosition.x = cursorPosition.x - (windowRect.left);
            windowCursorPosition.y = cursorPosition.y - (windowRect.top+31);
            std::cout << "window cursor position " << "x: " << windowCursorPosition.x << " : y: "<< windowCursorPosition.y << std::endl;
            model->handleMouse(windowCursorPosition.x, windowCursorPosition.y);
            std::cout << std::endl;
        }
        // OnMouseMove(hwnd, (UINT)wParam, cursorPosition.x, cursorPosition.y);
        draw();
        break;
    }
    case WM_LBUTTONDOWN:
    {
        std::cout << "mouse left button down" << std::endl;
        xPos = GET_X_LPARAM(lParam); 
        yPos = GET_Y_LPARAM(lParam); 
        draw();
        break;
    }
    case WM_RBUTTONDOWN:
    {
        std::cout << "mouse right button down" << std::endl;
        xPos = GET_X_LPARAM(lParam); 
        yPos = GET_Y_LPARAM(lParam); 
        draw();
        break;
    
    }
    case WM_MBUTTONDOWN:
    {
        std::cout << "mouse middle button down" << std::endl;
        xPos = GET_X_LPARAM(lParam); 
        yPos = GET_Y_LPARAM(lParam); 
        draw();
        break;

    }
    case WM_MOUSEWHEEL:
    {
        double fwKeys = GET_KEYSTATE_WPARAM(wParam);
        double zDelta = GET_WHEEL_DELTA_WPARAM(wParam);
        xPos = GET_X_LPARAM(lParam); 
        yPos = GET_Y_LPARAM(lParam); 
        handleScroll(fwKeys, zDelta, xPos, yPos);
        draw();
        break;
    }
    case WM_SIZE:
    {
        uint32_t width = LOWORD(lParam);  // Macro to get the low-order word.
        uint32_t height = HIWORD(lParam); // Macro to get the high-order word.

        if (bSize == false)
        {
            bSize = true;
        }
        else
        {   
            // Respond to the message:
            handleSize((UINT)wParam, width, height);
            draw();
        }
        return 0;
    }
    case WM_PAINT:
        draw();
        return 0;
    default:
        return DefWindowProc(m_hwnd, uMsg, wParam, lParam);
    }

    return TRUE;
}

void HWindow::handleSize(UINT flag, uint32_t width, uint32_t height)
{
    model->resizeFramebuffer(width, height);
}

/*
 * https://stackoverflow.com/questions/1903954/is-there-a-standard-sign-function-signum-sgn-in-c-c
 */
template <typename T> int sgn(T val)
{
    return (T(0) < val) - (val < T(0));
}

template <typename T> inline constexpr
int signum(T x, std::false_type is_signed)
{
    return T(0) < x;
}

template <typename T> inline constexpr
int signum(T x, std::true_type is_signed) 
{
    return (T(0) < x) - (x < T(0));
}

template <typename T> inline constexpr
int signum(T x) 
{
    return signum(x, std::is_signed<T>());
}

void HWindow::handleScroll(double keystate, double scrollDelta, double xpos, double ypos)
{
    float sensitivity = 0.01;
    int8_t sign = sgn(scrollDelta);
    if (currentKeystate != sign)
    {
        scrollPosition = 0;
    }
    currentKeystate = sign;

    scrollPosition += sensitivity * scrollDelta;
    std::cout << "scroll keystate: " << keystate << "\n"
              << "scroll delta: " << scrollDelta << "\n"
              << "scroll delta position: " << scrollPosition << "\n"
              << "scroll xpos: " << xpos << "\n"
              << "scroll ypos: " << ypos << "\n"
              << std::endl;

    if (sign > 0)
    {
        std::cout << "UP" << std::endl;
        model->transform(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1);
        model->transform(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2);
    }
    else
    {
        std::cout << "DOWN" << std::endl;
        model->transform(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1);
        model->transform(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2);
    }
}