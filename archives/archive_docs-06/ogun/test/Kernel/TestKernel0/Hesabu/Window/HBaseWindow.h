/**
 * @header
 * @copyright
 * @brief
 * @note 
 */


#pragma once
#ifndef HBaseWindow_h
#define HBaseWindow_h

#ifdef PLATFORM_VIDEO_WINDOWS
#include <Windows.h>
#endif

#ifdef PLATFORM_APPLE_MACOS
#import <AppKit/NSView.h>
#import <AppKit/NSWindow.h>
#endif

#ifdef PLATFORM_APPLE_IOS
#import <UIKit/UIWindow.h>
#endif

#ifdef PLATFORM_VIDEO_APPLE
#import <QuartzCore/CAMetalLayer.h>
#endif

#include <windows.h>
#include <string>

namespace hesabu
{

struct HBaseWindowInfo
{};

enum class HWindowMode
{
    HIDDEN = 0,
    NORMAL = 1,
    MINIMIZED = 2,
    MAXIMIZED = 3,
    INACTIVE = 4,
    SHOW = 5,
    MINIMIZE = 6,
    INACTIVE_MIN = 7,
    NA = 8,
    RESTORE = 9,
    DEFAULT = 10,
    FORCE_MINIMIZE = 11
};

template <class DERIVED_TYPE> 
class HBaseWindow
{
public:
    HBaseWindow() : m_name(DEFAULT_WINDOW_NAME), m_hwnd(NULL)
                  , m_width(DEFAULT_WIDTH), m_height(DEFAULT_HEIGHT) {}

    HBaseWindow(std::string name) : m_name(name), m_hwnd(NULL) {}

    virtual ~HBaseWindow(void) = default;

    void show(uint32_t mode = 1)
    {
        ShowWindow(m_hwnd, mode);
    }

    void message()
    {
        MSG msg = { };
        BOOL bRet;
        while ((bRet = GetMessage(&msg, NULL, 0, 0)) != 0)
        {
            if (bRet == -1)
            {
                // handle error
            }
            else
            {
                TranslateMessage(&msg);
                DispatchMessage(&msg);
            }
        }
    }

    static LRESULT CALLBACK WindowProc(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam)
    {
        DERIVED_TYPE *pThis = NULL;

        if (uMsg == WM_NCCREATE)
        {
            CREATESTRUCT* pCreate = (CREATESTRUCT*)lParam;
            pThis = (DERIVED_TYPE*)pCreate->lpCreateParams;
            SetWindowLongPtr(hwnd, GWLP_USERDATA, (LONG_PTR)pThis);
            pThis->m_hwnd = hwnd;
        }
        else
        {
            pThis = (DERIVED_TYPE*)GetWindowLongPtr(hwnd, GWLP_USERDATA);
        }
        if (pThis)
        {
            return pThis->HandleMessage(uMsg, wParam, lParam);
        }
        else
        {
            return DefWindowProc(hwnd, uMsg, wParam, lParam);
        }
    }

    BOOL Create(
        PCWSTR lpWindowName,
        DWORD dwStyle,
        DWORD dwExStyle = 0,
        int x = CW_USEDEFAULT,
        int y = CW_USEDEFAULT,
        int nWidth = CW_USEDEFAULT,
        int nHeight = CW_USEDEFAULT,
        HWND hWndParent = 0,
        HMENU hMenu = 0
        )
    {
        WNDCLASS wc = {0};

        wc.lpfnWndProc   = DERIVED_TYPE::WindowProc;
        wc.hInstance     = GetModuleHandle(NULL);
        wc.lpszClassName = "hesabu window";

        RegisterClass(&wc);

        m_hwnd = CreateWindowEx(
            dwExStyle, "hesabu window", "hesabu", dwStyle, x, y,
            nWidth, nHeight, hWndParent, hMenu, GetModuleHandle(NULL), this
            );

        return (m_hwnd ? TRUE : FALSE);
    }

    HWND hwnd() const { return m_hwnd; }

    std::string name() const { return m_name; }

    uint32_t width() const { return m_width; }

    uint32_t height() const { return m_height; }

protected:

    virtual LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam) = 0;

    HWND m_hwnd;

    std::string m_name;
    
    const std::string DEFAULT_WINDOW_NAME = "Hesabu Window";

private:

    uint32_t m_width;

    uint32_t m_height;

    const uint32_t DEFAULT_WIDTH = 600;

    const uint32_t DEFAULT_HEIGHT = 800;
};

} // namespace hesabu

#endif // HBaseWindow_h