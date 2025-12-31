/**
 * @copyright
 * @brief
 * @note 
 */

 #pragma once
 #ifndef hbasewindow_h
 #define hbasewindow_h
 
// #ifdef PLATFORM_WINDOWS
#include <Windows.h>
// #endif

// #ifdef PLATFORM_LINUX
// #include <X11/Xlib.h>
// #include <X11/Xutil.h>
// #endif


#include <string>
#include "hesabu/core/window/hstructures.h"

namespace hesabu
{

enum class HWindowMode
{
    HWS_HIDDEN = 0u,
    HWS_NORMAL = 1u,
    HWS_MINIMIZE = 2u,
    HWS_MAXIMIZE = 3u,
};

class HBaseWindow
{
public:
    HBaseWindow()
        : m_name("hesabu")
        , m_extent(HExtent{600u, 800u})
        , m_origin{HPoint{0u, 0u}}
        , m_active(false)
        , m_status(0u)
    {}

    virtual ~HBaseWindow() = default;

    /**
     * create a new window
     */
    virtual void create(std::string name) = 0;

    /**
     * show window
     * @param mode display mode
     */
    virtual void show(HWindowMode mode) = 0;

    /**
     * poll window event
     * @param event updated event polled
     */
    virtual void poll() = 0;
    
    /**
     * handle window event
     */
    virtual void handleEvent() = 0;

    // /**
    //  * handle key event
    //  */
    // virtual void handleKeyEvent() = 0;

    // /**
    //  * handle cursor event
    //  */
    // virtual void handleCursorEvent() = 0;

    // /**
    //  * handle mouse event
    //  */
    // virtual void handleMouseEvent() = 0;

    // /**
    //  * handle scroll event
    //  */
    // virtual void handleScrollEvent() = 0;

    // /**
    //  * handle screen event
    //  */
    // virtual void handleScreenEvent() = 0;

    /**
     * get window extent
     * @return width and height extent of window
     */
    HExtent extent() const { return m_extent; }

    /**
     * get name of window
     * @return name of window
     */
    std::string name() const { return m_name; }

    /**
     * get window active state
     * @return is window active
     */
    bool active() const { return m_active; }
    
    /**
     * set window to active
     */
    void activate() { m_active = true; }

    /**
     * set window to inactive
     */
    void deactivate() { m_active = false; }

protected:

    uint8_t m_status;

private:

    bool m_active;

    HExtent m_extent;
    
    HPoint m_origin;

    std::string m_name;

    const HExtent DEFAULT_EXTENT = {600u, 800u};
    
    const HPoint DEFAULT_ORIGIN = {0u, 0u};

    const std::string DEFAULT_NAME = "hesabu";
};

template<class DERIVED_TYPE>
class HBaseWindowWin32 : public HBaseWindow
{
public:
    HBaseWindowWin32()
        : HBaseWindow()
    {}
    ~HBaseWindowWin32() = default;

    /**
     * get handle to window
     * @return handle to current window
     */
    HWND hwnd() const { return m_hwnd; }

    /**
     * create a new window
     */
    void create(std::string name)
    {
        std::wstring namew = std::wstring(name.begin(), name.end());
        m_status = Create(namew.c_str(), WS_OVERLAPPEDWINDOW);
    }

    /**
     * show window
     * @param mode display mode
     */
    void show(HWindowMode mode)
    {
        m_status = ShowWindow(m_hwnd, (uint8_t)mode);
    }

    /**
     * poll window event
     */
    void poll()
    {
        MSG msg = {};
        BOOL bRet;
        bRet = GetMessage(&msg, NULL, 0, 0);
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }
    
    /**
     * handle window event
     */
    void handleEvent()
    {
        
    }
    
protected:
    /**
     * handle window message
     * @param uMsg
     * @param wParam
     * @param lParam
     */
    virtual LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam) = 0;

private:
    /**
     * create new window internal
     * @param lpWindowName
     * @param dwStyle
     * @param dwExStyle
     * @param x
     * @param y
     * @param nWidth
     * @param nHeight
     * @param hWndParent
     * @param hMenu
     * @return handle to created window
     */
    BOOL Create(
        PCWSTR lpWindowName,
        DWORD dwStyle,
        DWORD dwExStyle = 0u,
        int x = CW_USEDEFAULT,
        int y = CW_USEDEFAULT,
        int nWidth = 800u,
        int nHeight = 600u,
        HWND hWndParent = 0u,
        HMENU hMenu = 0u
        )
    {
        // register window callback process
        WNDCLASS wc = {0u};
        wc.lpfnWndProc   = DERIVED_TYPE::WindowProc;
        wc.hInstance     = GetModuleHandle(NULL);
        wc.lpszClassName = "hesabu";
        RegisterClass(&wc);

        // create new window
        m_hwnd = CreateWindowEx(
            dwExStyle, "hesabu", "hesabu", dwStyle, x, y,
            nWidth, nHeight, hWndParent, hMenu,
            GetModuleHandle(NULL), this
            );

        return (m_hwnd ? TRUE : FALSE);
    }

    /**
     * window message callback
     * @param hwnd
     * @param uMsg
     * @param wParam
     * @param lParam
     */
    static LRESULT CALLBACK WindowProc(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam)
    {
        DERIVED_TYPE *pThis = NULL;
        int index; 
        static HMENU hmenu;

        if (uMsg == WM_NCCREATE)
        {
            CREATESTRUCT* pCreate = (CREATESTRUCT*)lParam;
            pThis = (DERIVED_TYPE*)pCreate->lpCreateParams;
            SetWindowLongPtr(hwnd, GWLP_USERDATA, (LONG_PTR)pThis);
            pThis->m_hwnd = hwnd;
            pThis->activate();
            hmenu = GetMenu(hwnd);
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

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK CallWndProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK CBTProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK DebugProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK GetMsgProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK KeyboardProc(int nCode, WPARAM wParam, LPARAM lParam) 
    { 
        CHAR szBuf[128]; 
        HDC hdc; 
        static int c = 0u; 
        size_t cch; 
        HRESULT hResult;
    }

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK MessageProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK MouseProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK ShellProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    /**
     * keyboard callback process
     * @param nCode
     * @param wParam
     * @param lParam
     */
    LRESULT CALLBACK SysMsgProc(int nCode, WPARAM wParam, LPARAM lParam) 
    {}

    HWND m_hwnd;

};

};

#endif // hbasewindow_h