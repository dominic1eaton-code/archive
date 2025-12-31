/**
 * @copyright
 * @brief
 * @note 
 */

#include "core/window/hwindow.h"
#include "hbasewindow.h"

using namespace hesabu;

template<class DERIVED_TYPE> 
IHBaseWindowWin32<DERIVED_TYPE>::IHBaseWindowWin32()
    : _pimpl(new HBaseWindowWin32<DERIVED_TYPE>())
{}

template<class DERIVED_TYPE> 
IHBaseWindowWin32<DERIVED_TYPE>::~IHBaseWindowWin32()
{
    delete _pimpl;
}

template<class DERIVED_TYPE>
IHBaseWindowWin32<DERIVED_TYPE>::HBaseWindowWin32<DERIVED_TYPE>::HBaseWindowWin32()
{
    std::cout << "create window WIN32 interface" << std::endl;
}

class HBaseWindow
{
public:
    HBaseWindow()
        : m_name(DEFAULT_NAME)
        , m_extent(DEFAULT_EXTENT)
        , m_origin{DEFAULT_ORIGIN}
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
    virtual void show(uint8_t mode) = 0;

    /**
     * poll window event
     * @param event updated event polled
     */
    virtual void poll(HWindowEvent event) = 0;

    /**
     * handle key event
     */
    virtual void handleKeyEvent() = 0;

    /**
     * handle cursor event
     */
    virtual void handleCursorEvent() = 0;

    /**
     * handle mouse event
     */
    virtual void handleMouseEvent() = 0;

    /**
     * handle scroll event
     */
    virtual void handleScrollEvent() = 0;

    /**
     * handle screen event
     */
    virtual void handleScreenEvent() = 0;

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

    /**
     * get window status
     * @return current status of window
     */
    uint8_t status()  const { return m_status; }


protected:

    uint8_t m_status;

private:

    bool m_active;

    HExtent m_extent;
    
    HPoint m_origin;

    std::string m_name;

    const HExtent DEFAULT_EXTENT{600u, 800u};
    
    const HPoint DEFAULT_ORIGIN{0u, 0u};

    const std::string DEFAULT_NAME = "hesabu";
};

// template<class DTYPE>
// class HBaseWindowUnix : public HBaseWindow
// {
// public:
//     HBaseWindowUnix() = default;
//     virtual ~HBaseWindowUnix(void) = default;

// };



template<class DTYPE>
class IHBaseWindowWin32<DTYPE>::HBaseWindowWin32// : public HBaseWindow
{
public:
    HBaseWindowWin32() = default;

    virtual ~HBaseWindowWin32(void) = default;

    /**
     * get handle to window
     * @return handle to current window
     */
    HWND hwnd() const { return m_hwnd; }

    /**
     * create a new window
     * @param name name of window to create
     */
    virtual void create(std::string name)
    {
        std::wstring namew = std::wstring(name.begin(), name.end());
        m_status = Create(namew.c_str(), WS_OVERLAPPEDWINDOW);
    }

    /**
     * show window
     * @param mode display mode
     */
    virtual void show(uint8_t mode)
    {
        m_status = ShowWindow(m_hwnd, mode);
    }

    /**
     * poll window event
     * @param event updated event polled
     */
    virtual void poll(HWindowEvent event)
    {
        MSG msg = {};
        BOOL bRet;
        bRet = GetMessage(&msg, NULL, 0, 0);
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }

    /**
     * handle key event
     */
    virtual void handleKeyEvent() = 0;

    /**
     * handle cursor event
     */
    virtual void handleCursorEvent() = 0;

    /**
     * handle mouse event
     */
    virtual void handleMouseEvent() = 0;

    /**
     * handle scroll event
     */
    virtual void handleScrollEvent() = 0;

    /**
     * handle screen event
     */
    virtual void handleScreenEvent() = 0;

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
        wc.lpfnWndProc   = DTYPE::WindowProc;
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
        DTYPE *pThis = NULL;
        int index; 
        static HMENU hmenu;

        if (uMsg == WM_NCCREATE)
        {
            CREATESTRUCT* pCreate = (CREATESTRUCT*)lParam;
            pThis = (DTYPE*)pCreate->lpCreateParams;
            SetWindowLongPtr(hwnd, GWLP_USERDATA, (LONG_PTR)pThis);
            pThis->m_hwnd = hwnd;
            pThis->activate();
            hmenu = GetMenu(hwnd);
        }
        else
        {
            pThis = (DTYPE*)GetWindowLongPtr(hwnd, GWLP_USERDATA);
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

template<class DTYPE>
IHBaseWindowWin32<DTYPE>::IHBaseWindowWin32()
    : pImpl(new HBaseWindowWin32())
{}

template<class DTYPE>
IHBaseWindowWin32<DTYPE>::~IHBaseWindowWin32() = default;

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
        return DefWindowProc(pimpl->hwnd(), uMsg, wParam, lParam);
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
