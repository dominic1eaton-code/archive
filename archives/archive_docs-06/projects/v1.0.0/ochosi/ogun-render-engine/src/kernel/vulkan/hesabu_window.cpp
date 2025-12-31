/**
 * @copyright
 * @brief
 * @note
 */

#include "hesabu_window.h"
#include "vulkan_engine.h"
#include <windowsx.h>
#include <iostream>

#ifndef SAFE_RELEASE
#define SAFE_RELEASE(p) { if (p) { (p)->Release(); (p) = nullptr; } }
#endif
namespace hesabu
{

float window_tick = .000001f;
float current_scroll_position = 0.0f;
double current_key_state = 0;
vulkan::VFrame* vulkan_frame;
/* opaque; particle; transparent; translucent; blur */
std::vector<bool> passes_enabled = {true, true};

void run_app()
{
    HWND hwnd;
    uint32_t width;
    uint32_t height;
    init_window(hwnd, width, height);
    poll_window();
    // message_window();
}

void init_window(HWND& hwnd, uint32_t& width, uint32_t& height)
{
    HWindowState window;
    create_window(window, hwnd);
    ShowWindow(hwnd, SW_SHOW);
    width = window.nWidth;
    height = window.nHeight;
}

void poll_window()
{
    MSG msg = {};
    // bRet = GetMessage(&msg, NULL, 0, 0);
    // TranslateMessage(&msg);
    // DispatchMessage(&msg);
    while (PeekMessageW(&msg, NULL, 0, 0, PM_REMOVE))
    {
        window_tick += .0001f;
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }
    BOOL bRet;
}

BOOL create_window(HWindowState window, HWND& hwnd)
{
    WNDCLASS wc = {0};
    wc.lpfnWndProc   = HWindowProc;
    wc.hInstance     = window.hInstance;
    wc.lpszClassName = "hesabu";
    
    if (!RegisterClass(&wc))
    {
        DWORD error = GetLastError();
    }

    HWindowState *pState = new (std::nothrow) HWindowState;
    if (pState == NULL)
    {
        return 0;
    }

    hwnd = CreateWindowEx(
        window.dwExStyle, "hesabu", "hesabu",
        window.dwStyle, window.x, window.y,
        window.nWidth, window.nHeight, window.hWndParent,
        window.hMenu, window.hInstance, pState
        );
    return (hwnd ? TRUE : FALSE);
}

static LRESULT handle_window_message(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    // render model update
    vulkan::draw_frame(window_tick, vulkan_frame);

    // input update
    // handle_mouse(wParam, lParam);

    // window update
    // window state
    const HWND desktop_window = GetDesktopWindow();
    RECT desktop_screen;
    RECT app_screen;
    POINT desktop_cursor_position;
    POINT app_cursor_position;
    GetWindowRect(desktop_window, &desktop_screen);
    GetWindowRect(hwnd, &app_screen);

    switch (uMsg)
    {
    case WM_DESTROY:
    {
        cleanup_window();
        PostQuitMessage(0);
        return 0;
    }
    case WM_SIZE:
    {
        int width = LOWORD(lParam);  // Macro to get the low-order word.
        int height = HIWORD(lParam); // Macro to get the high-order word.
        handle_resize((UINT)wParam, (uint32_t)width, (uint32_t)height);
        // vulkan::draw_frame(tick, vulkan_frame);
        break;
    }
    case WM_PAINT:
    {
        // vulkan::draw_frame(tick, vulkan_frame);
        return 0;
    }
    case WM_KEYDOWN:
    {
        handle_key_press(wParam);
    }
    case WM_MOUSEMOVE:
    {
        float cursor_ndc_x;
        float cursor_ndc_y;
        GetCursorPos(&desktop_cursor_position);
        ScreenToClient(hwnd, &desktop_cursor_position);
        double normalizedX = (-1.0 + 2.0 * (double)desktop_cursor_position.x / (app_screen.left - app_screen.right)) + 2.0f; 
        double normalizedY = (1.0 - 2.0 * (double)desktop_cursor_position.y / (app_screen.top - app_screen.bottom)) - 2.0f;
        // GetCursorPos(&app_cursor_position);
        // app_cursor_position.x = desktop_cursor_position.x - app_screen.left;
        // app_cursor_position.y = desktop_cursor_position.y - app_screen.top;
        // cursor_ndc_x = ((2.0f * app_cursor_position.x) / (app_screen.left - app_screen.right) - 1.0f);
        // cursor_ndc_y = (1.0f - (2.0f * app_cursor_position.y) / (app_screen.top - app_screen.bottom));
        // cursor_ndc.x = 2*(app_cursor_position.x / (app_screen.left - app_screen.right)) - 1;
        // cursor_ndc.y = 2*(app_cursor_position.y / (app_screen.top - app_screen.bottom)) - 1;
        // std::cout << "desktop screen left : top : right : bottom " << desktop_screen.left << " : "  << desktop_screen.top << " : " << desktop_screen.right << " : "  << desktop_screen.bottom << std::endl;
        // std::cout << "app screen left : top : right : bottom " << app_screen.left << " : "  << app_screen.top << " : "  << app_screen.right << " : "  << app_screen.bottom << std::endl;
        // std::cout << "app cursor position x : y " << app_cursor_position.x << " : "  << app_cursor_position.y << std::endl;
        // std::cout << "cursor_ndc position x : y " << cursor_ndc_x << " : "  << cursor_ndc_y << std::endl;
        // std::cout << "desktop cursor position x : y " << desktop_cursor_position.x << " : "  << desktop_cursor_position.y << std::endl;
        // std::cout << "normalized cursor position x : y " << normalizedX << " : "  << normalizedY << std::endl;
        handle_cursor(normalizedX, normalizedY);
        break;
    }
    case WM_LBUTTONDOWN:
    {
        
        break;
    }
    case WM_RBUTTONDOWN:
    {

        break;
    }
    case WM_MBUTTONDOWN:
    {

        break;
    }
    case WM_MOUSEWHEEL:
    {
        double fwKeys = GET_KEYSTATE_WPARAM(wParam);
        double zDelta = GET_WHEEL_DELTA_WPARAM(wParam);
        double xPos = GET_X_LPARAM(lParam); 
        double yPos = GET_Y_LPARAM(lParam); 
        handle_scroll(fwKeys, zDelta, xPos, yPos);
        break;
    }
    default:
        // vulkan::draw_frame(tick, vulkan_frame);
        return DefWindowProc(hwnd, uMsg, wParam, lParam);
    }
    return TRUE;
}

static LRESULT CALLBACK HWindowProc(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam)
{
    HWindowState* pState = NULL;
    if (uMsg == WM_CREATE)
    {
        CREATESTRUCT *pCreate = reinterpret_cast<CREATESTRUCT*>(lParam);
        pState = reinterpret_cast<HWindowState*>(pCreate->lpCreateParams);
        SetWindowLongPtr(hwnd, GWLP_USERDATA, (LONG_PTR)pState);
        vulkan_frame = new vulkan::VFrame();
        vulkan_frame->passes_enabled = passes_enabled;
        vulkan::init_Vulkan(hwnd, VkExtent2D{pState->nWidth, pState->nHeight}, vulkan_frame);
    }
    else
    {
        pState = get_window_state(hwnd);
    }

    if (pState)
    {
        return handle_window_message(hwnd, uMsg, wParam, lParam);
    }
    else
        return DefWindowProc(hwnd, uMsg, wParam, lParam);
}

void message_window()
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

void handle_key_press(WPARAM wParam)
{
    switch (wParam)
    {
        case 0x31:
            break;
        case 0x32:
            break;
        case 0x33:
            break;
        case 0x34:
            break;
        case 0x35:
            break;
        case 0x36:
            break;
        case 0x37:
            break;
        case 0x38:
            break;
        case 0x39:
            break;
        case VK_NUMPAD0:
            vulkan::zoom_camera(vulkan_frame->scene.primary_camera, 1);
            break;
        case VK_NUMPAD1:
            vulkan::zoom_camera(vulkan_frame->scene.primary_camera, -1);
            break;
        case VK_NUMPAD2:
            vulkan::rotate_camera(vulkan_frame->scene.primary_camera, glm::radians(1.0f), glm::vec3(1.0f, 0.0f, 0.0f));
            break;
        case VK_NUMPAD3:
            vulkan::rotate_camera(vulkan_frame->scene.primary_camera, -glm::radians(1.0f), glm::vec3(1.0f, 0.0f, 0.0f));
            break;
        case VK_NUMPAD4:
            vulkan::rotate_camera(vulkan_frame->scene.primary_camera, glm::radians(1.0f), glm::vec3(0.0f, 1.0f, 0.0f));
            break;
        case VK_NUMPAD5:
            vulkan::rotate_camera(vulkan_frame->scene.primary_camera, -glm::radians(1.0f), glm::vec3(0.0f, 1.0f, 0.0f));
            break;
        case VK_NUMPAD6:
            vulkan::rotate_camera(vulkan_frame->scene.primary_camera, glm::radians(1.0f), glm::vec3(0.0f, 0.0f, 1.0f));
            break;
        case VK_NUMPAD7:
            vulkan::rotate_camera(vulkan_frame->scene.primary_camera, -glm::radians(1.0f), glm::vec3(0.0f, 0.0f, 1.0f));
            break;
        case VK_NUMPAD8:
            break;
        case VK_NUMPAD9:
            break;
        case VK_F1:
            break;
        case VK_F2:
            break;
        case VK_F3:
            break;
        case VK_F4:
            break;
        case VK_F5:
            break;
        case VK_F6:
            break;
        case VK_F7:
            break;
        case VK_F8:
            break;
        case VK_F9:
            break;
        case VK_F10:
            break;
        case VK_F11:
            break;
        case VK_F12:
            break;
        case VK_MULTIPLY:
            break;
        case VK_ADD:
            break;
        case VK_SEPARATOR:
            break;
        case VK_SUBTRACT:
            break;
        case VK_DECIMAL:
            break;
        case VK_DIVIDE:
            break;
        case VK_UP:
            vulkan::translate_camera(1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 1, vulkan_frame->scene.primary_camera);
            vulkan::translate_camera(1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 2, vulkan_frame->scene.primary_camera);
            break;
        case VK_DOWN:
            vulkan::translate_camera(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 1, vulkan_frame->scene.primary_camera);
            vulkan::translate_camera(-1.0f, glm::vec3(0.0f, 1.0f, 0.0f), 2, vulkan_frame->scene.primary_camera);
            break;
        case VK_LEFT:
            vulkan::translate_camera(1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 1, vulkan_frame->scene.primary_camera);
            vulkan::translate_camera(1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 2, vulkan_frame->scene.primary_camera);
            break;
        case VK_RIGHT:
            vulkan::translate_camera(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 1, vulkan_frame->scene.primary_camera);
            vulkan::translate_camera(-1.0f, glm::vec3(1.0f, 0.0f, 0.0f), 2, vulkan_frame->scene.primary_camera);
            break;
        case 'A':
            vulkan_frame->passes_enabled[0] = (vulkan_frame->passes_enabled[0] == true) ? false : true;
            break;
        case 'B':
            vulkan_frame->passes_enabled[1] = (vulkan_frame->passes_enabled[1] == true) ? false : true;
            break;
        case 'C':
            break;
        case 'D':
            break;
        case 'E':
            break;
        case 'F':
            break;
        case 'G':
            break;
        case 'H':
            break;
        case 'I':
            break;
        case 'J':
            break;
        case 'K':
            break;
        case 'L':
            break;
        case 'M':
            break;
        case 'N':
            break;
        case 'O':
            break;
        case 'P':
            vulkan::change_camera_perspective(vulkan_frame->scene.primary_camera);
            break;
        case 'Q':
            break;
        case 'R':
            break;
        case 'S':
            break;
        case 'T':
            break;
        case 'U':
            break;
        case 'V':
            break;
        case 'W':
            break;
        case 'X':
            break;
        case 'Y':
            break;
        case 'Z':
            break;
        default:
            break;
    }
}

void handle_mouse(WPARAM wParam, LPARAM lParam)
{
    switch (wParam)
    {
        case WM_MOUSEMOVE:
        {

        }
        case WM_LBUTTONDOWN:
        {
            
        }
        case WM_RBUTTONDOWN:
        {

        }
        case WM_MBUTTONDOWN:
        {

        }
        case WM_MOUSEWHEEL:
        {
            double fwKeys = GET_KEYSTATE_WPARAM(wParam);
            double zDelta = GET_WHEEL_DELTA_WPARAM(wParam);
            double xPos = GET_X_LPARAM(lParam); 
            double yPos = GET_Y_LPARAM(lParam); 
            handle_scroll(fwKeys, zDelta, xPos, yPos);
        }
    }
}

void handle_cursor(double xpos, double ypos)
{
    vulkan::move_cursor(xpos, ypos, vulkan_frame->cursor);
}

void handle_scroll(double keystate, double scrollDelta, double xpos, double ypos)
{
    float sensitivity = 0.01;
    int8_t sign = vulkan::sgn(scrollDelta);
    if (current_key_state != sign)
    {
        current_scroll_position = 0;
    }
    current_key_state = sign;
    current_scroll_position += sensitivity * scrollDelta;

    if (sign > 0)
    {
        vulkan::translate_camera(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1, vulkan_frame->scene.primary_camera);
        vulkan::translate_camera(1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2, vulkan_frame->scene.primary_camera);
    }
    else
    {
        vulkan::translate_camera(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 1, vulkan_frame->scene.primary_camera);
        vulkan::translate_camera(-1.0f, glm::vec3(0.0f, 0.0f, 1.0f), 2, vulkan_frame->scene.primary_camera);
    }
}

void handle_resize(UINT flag, uint32_t width, uint32_t height)
{
    vulkan::resize_frame_buffer(width, height, vulkan_frame);
}

void handle_gamepad()
{
    UINT nDevices = 0;
    GetRawInputDeviceList(NULL, &nDevices, sizeof(RAWINPUTDEVICELIST));
    if (nDevices < 1)
        return;

    PRAWINPUTDEVICELIST pRawInputDeviceList;
    pRawInputDeviceList = new RAWINPUTDEVICELIST[sizeof(RAWINPUTDEVICELIST) * nDevices];
    if (pRawInputDeviceList == NULL)
        return;

    int nResult;
    nResult = GetRawInputDeviceList(pRawInputDeviceList, &nDevices, sizeof(RAWINPUTDEVICELIST));
    

    if (nResult < 0)
    {
        delete[] pRawInputDeviceList;
    }

    for (UINT i = 0; i < nDevices; i++)
    {
        UINT nBufferSize = 0;
        nResult = GetRawInputDeviceInfo(pRawInputDeviceList[i].hDevice,
            RIDI_DEVICENAME,
            NULL,
            &nBufferSize);

        if (nResult < 0)
            continue;

        WCHAR* wcDeviceName = new WCHAR[nBufferSize + 1];

        if (wcDeviceName == NULL)
            continue;
        
        nResult = GetRawInputDeviceInfo(pRawInputDeviceList[i].hDevice,
            RIDI_DEVICENAME,
            wcDeviceName,
            &nBufferSize);

        if (nResult < 0)
        {
            delete[] wcDeviceName;
            continue;
        }

        RID_DEVICE_INFO rdiDeviceInfo;
        rdiDeviceInfo.cbSize = sizeof(RID_DEVICE_INFO);
        nBufferSize = rdiDeviceInfo.cbSize;

        nResult = GetRawInputDeviceInfo(pRawInputDeviceList[i].hDevice,
            RIDI_DEVICEINFO,
            &rdiDeviceInfo,
            &nBufferSize);
            
        if (nResult < 0)
            continue;

        if (rdiDeviceInfo.dwType == RIM_TYPEMOUSE)
        {

        }
        else if (rdiDeviceInfo.dwType == RIM_TYPEKEYBOARD)
        {

        }
        else
        {

        }
        delete[] wcDeviceName;
    }
    delete[] pRawInputDeviceList;
}

BOOL IsXInputDevice( const GUID* pGuidProductFromDirectInput )
{
    IWbemLocator*           pIWbemLocator = nullptr;
    IEnumWbemClassObject*   pEnumDevices = nullptr;
    IWbemClassObject*       pDevices[20] = {};
    IWbemServices*          pIWbemServices = nullptr;
    BSTR                    bstrNamespace = nullptr;
    BSTR                    bstrDeviceID = nullptr;
    BSTR                    bstrClassName = nullptr;
    bool                    bIsXinputDevice = false;
    
    // CoInit if needed
    HRESULT hr = CoInitialize(nullptr);
    bool bCleanupCOM = SUCCEEDED(hr);

    // So we can call VariantClear() later, even if we never had a successful IWbemClassObject::Get().
    VARIANT var = {};
    VariantInit(&var);

    // Create WMI
    hr = CoCreateInstance(__uuidof(WbemLocator),
        nullptr,
        CLSCTX_INPROC_SERVER,
        __uuidof(IWbemLocator),
        (LPVOID*)&pIWbemLocator);
    if (FAILED(hr) || pIWbemLocator == nullptr)
        goto LCleanup;

    bstrNamespace = SysAllocString(L"\\\\.\\root\\cimv2");  if (bstrNamespace == nullptr) goto LCleanup;
    bstrClassName = SysAllocString(L"Win32_PNPEntity");     if (bstrClassName == nullptr) goto LCleanup;
    bstrDeviceID = SysAllocString(L"DeviceID");             if (bstrDeviceID == nullptr)  goto LCleanup;
    
    // Connect to WMI 
    hr = pIWbemLocator->ConnectServer(bstrNamespace, nullptr, nullptr, 0L,
        0L, nullptr, nullptr, &pIWbemServices);
    if (FAILED(hr) || pIWbemServices == nullptr)
        goto LCleanup;

    // Switch security level to IMPERSONATE. 
    hr = CoSetProxyBlanket(pIWbemServices,
        RPC_C_AUTHN_WINNT, RPC_C_AUTHZ_NONE, nullptr,
        RPC_C_AUTHN_LEVEL_CALL, RPC_C_IMP_LEVEL_IMPERSONATE,
        nullptr, EOAC_NONE);
    if ( FAILED(hr) )
        goto LCleanup;

    hr = pIWbemServices->CreateInstanceEnum(bstrClassName, 0, nullptr, &pEnumDevices);
    if (FAILED(hr) || pEnumDevices == nullptr)
        goto LCleanup;

    // Loop over all devices
    for (;;)
    {
        ULONG uReturned = 0;
        hr = pEnumDevices->Next(10000, _countof(pDevices), pDevices, &uReturned);
        if (FAILED(hr))
            goto LCleanup;
        if (uReturned == 0)
            break;

        for (size_t iDevice = 0; iDevice < uReturned; ++iDevice)
        {
            // For each device, get its device ID
            hr = pDevices[iDevice]->Get(bstrDeviceID, 0L, &var, nullptr, nullptr);
            if (SUCCEEDED(hr) && var.vt == VT_BSTR && var.bstrVal != nullptr)
            {
                // Check if the device ID contains "IG_".  If it does, then it's an XInput device
                // This information cannot be found from DirectInput 
                if (wcsstr(var.bstrVal, L"IG_"))
                {
                    // If it does, then get the VID/PID from var.bstrVal
                    DWORD dwPid = 0, dwVid = 0;
                    WCHAR* strVid = wcsstr(var.bstrVal, L"VID_");
                    if (strVid && swscanf_s(strVid, L"VID_%4X", &dwVid) != 1)
                        dwVid = 0;
                    WCHAR* strPid = wcsstr(var.bstrVal, L"PID_");
                    if (strPid && swscanf_s(strPid, L"PID_%4X", &dwPid) != 1)
                        dwPid = 0;

                    // Compare the VID/PID to the DInput device
                    DWORD dwVidPid = MAKELONG(dwVid, dwPid);
                    if (dwVidPid == pGuidProductFromDirectInput->Data1)
                    {
                        bIsXinputDevice = true;
                        goto LCleanup;
                    }
                }
            }
            VariantClear(&var);
            SAFE_RELEASE(pDevices[iDevice]);
        }
    }

LCleanup:
    VariantClear(&var);
    
    if(bstrNamespace)
        SysFreeString(bstrNamespace);
    if(bstrDeviceID)
        SysFreeString(bstrDeviceID);
    if(bstrClassName)
        SysFreeString(bstrClassName);
        
    for (size_t iDevice = 0; iDevice < _countof(pDevices); ++iDevice)
        SAFE_RELEASE(pDevices[iDevice]);

    SAFE_RELEASE(pEnumDevices);
    SAFE_RELEASE(pIWbemLocator);
    SAFE_RELEASE(pIWbemServices);

    if(bCleanupCOM)
        CoUninitialize();

    return bIsXinputDevice;
}

void cleanup_window()
{
    delete vulkan_frame;
}

}