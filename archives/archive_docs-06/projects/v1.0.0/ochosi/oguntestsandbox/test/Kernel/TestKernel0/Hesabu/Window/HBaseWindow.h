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
#include <strsafe.h>

#pragma comment( lib, "user32.lib") 
#pragma comment( lib, "gdi32.lib")


namespace hesabu
{


#define IDM_CALLWNDPROC 0
#define IDM_CBT 1
#define IDM_DEBUG 2
#define IDM_GETMESSAGE 3
#define IDM_KEYBOARD  4
#define IDM_MOUSE 5
#define IDM_MSGFILTER 6

#define NUMHOOKS 7 

struct HBaseWindowInfo
{};

/**
 * @brief window state
 */
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

    typedef struct _MYHOOKDATA 
    { 
        int nType; 
        HOOKPROC hkprc; 
        HHOOK hhook; 
    } MYHOOKDATA; 

    MYHOOKDATA myhookdata[NUMHOOKS]; 

    HBaseWindow() : m_name(DEFAULT_WINDOW_NAME), m_hwnd(NULL)
                  , m_width(DEFAULT_WIDTH), m_height(DEFAULT_HEIGHT) {}

    HBaseWindow(std::string name) : m_name(name), m_hwnd(NULL) {}

    virtual ~HBaseWindow(void) = default;

    /**
     * return window handle
     * @return window handle
     */
    HWND hwnd() const { return m_hwnd; }

    /**
     * return window name
     * @return window name
     */
    std::string name() const { return m_name; }

    /**
     * return window width
     * @return window width
     */
    uint32_t width() const { return m_width; }

    /**
     * return window height
     * @return window height
     */
    uint32_t height() const { return m_height; }

    /**
     * show window on screen
     * @param window state
     */
    void show(uint32_t mode = 1) { ShowWindow(m_hwnd, mode); }

    /**
     * @brief get window messages
     */
    void message()
    {
        MSG msg = {};
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

    /**
     * @brief window message callback
     */
    static LRESULT CALLBACK WindowProc(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam)
    {
        DERIVED_TYPE *pThis = NULL;

        if (uMsg == WM_NCCREATE)
        {
            CREATESTRUCT* pCreate = (CREATESTRUCT*)lParam;
            pThis = (DERIVED_TYPE*)pCreate->lpCreateParams;
            SetWindowLongPtr(hwnd, GWLP_USERDATA, (LONG_PTR)pThis);
            pThis->m_hwnd = hwnd;
            pThis->activate();
            // pThis->init();
        }
        else
        {
            pThis = (DERIVED_TYPE*)GetWindowLongPtr(hwnd, GWLP_USERDATA);
        }
        
        if (pThis)
        {
            // if (pThis->active()) pThis->update();
            return pThis->HandleMessage(uMsg, wParam, lParam);
        }
        else
        {
            return DefWindowProc(hwnd, uMsg, wParam, lParam);
        }
    }

    /**
     * @brief create new window
     */
    void create(std::wstring name)
    {
        if (!Create(name.c_str(), WS_OVERLAPPEDWINDOW)) { m_status = 1;}
    }

    /**
     * @brief create new window internal
     */
    BOOL Create(
        PCWSTR lpWindowName,
        DWORD dwStyle,
        DWORD dwExStyle = 0,
        int x = CW_USEDEFAULT,
        int y = CW_USEDEFAULT,
        int nWidth = 800,
        int nHeight = 600,
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

protected:

    /**
     * @brief handle window message
     */
    virtual LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam) = 0;

    /**
     * @brief initialize window
     */
    virtual void init() = 0;

    /**
     * @brief update window
     */
    virtual void update() = 0;

    /**
     * @brief is window active?
     */
    bool active() const { return m_active; }

    /**
     * @brief set window to active
     */
    void activate() { m_active = true; }

    /**
     * @brief set window to INactive
     */
    void deactivate() { m_active = false; }

    /**
     * @brief window handle
     */
    HWND m_hwnd;

    /**
     * @brief swindow name
     */
    std::string m_name;
    
    /**
     * @brief default window name
     */
    const std::string DEFAULT_WINDOW_NAME = "Hesabu Window";

private:

    /**
     * @brief is window active ?
     */
    bool m_active = false;

    /**
     * @brief window status
     */
    uint32_t m_status = 0;

    /**
     * @brief window display state
     */
    uint32_t m_nCmdShow = 1;

    /**
     * @brief current window width
     */
    uint32_t m_width;

    /**
     * @brief current window height
     */
    uint32_t m_height;

    /**
     * @brief defeault window width
     */
    const uint32_t DEFAULT_WIDTH = 600;


    /**
     * @brief defeault window height
     */
    const uint32_t DEFAULT_HEIGHT = 800;
};

} // namespace hesabu

#endif // HBaseWindow_h