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
#include <cmath>
// #include "XInputOnGameInput.h"


#ifndef SAFE_RELEASE
#define SAFE_RELEASE(p) { if (p) { (p)->Release(); (p) = nullptr; } }
#endif

using namespace hesabu;


/* https://stackoverflow.com/questions/36453082/c-winapi-get-list-of-all-connected-usb-devices */
void getinputdevices()
{
    // Program
    std::cout << "USB Device Lister." << std::endl;

    // Get Number Of Devices
    UINT nDevices = 0;
    GetRawInputDeviceList(NULL, &nDevices, sizeof(RAWINPUTDEVICELIST));

    // // Got Any?
    // if (nDevices < 1)
    // {
    //     // Exit
    //     cout << "ERR: 0 Devices?";
    //     cin.get();
    //     return 0;
    // }

    // Allocate Memory For Device List
    PRAWINPUTDEVICELIST pRawInputDeviceList;
    pRawInputDeviceList = new RAWINPUTDEVICELIST[sizeof(RAWINPUTDEVICELIST) * nDevices];

    // // Got Memory?
    // if (pRawInputDeviceList == NULL)
    // {
    //     // Error
    //     cout << "ERR: Could not allocate memory for Device List.";
    //     cin.get();
    //     return 0;
    // }

    // Fill Device List Buffer
    int nResult;
    nResult = GetRawInputDeviceList(pRawInputDeviceList, &nDevices, sizeof(RAWINPUTDEVICELIST));

    // Got Device List?
    if (nResult < 0)
    {
        // Clean Up
        delete[] pRawInputDeviceList;

        // // Error
        // cout << "ERR: Could not get device list.";
        // cin.get();
        // return 0;
    }

    // Loop Through Device List
    for (UINT i = 0; i < nDevices; i++)
    {
        // Get Character Count For Device Name
        UINT nBufferSize = 0;
        nResult = GetRawInputDeviceInfo(pRawInputDeviceList[i].hDevice, // Device
            RIDI_DEVICENAME,                // Get Device Name
            NULL,                           // NO Buff, Want Count!
            &nBufferSize);                 // Char Count Here!

                                           // Got Device Name?
        if (nResult < 0)
        {
            // Error
            std::cout << "ERR: Unable to get Device Name character count.. Moving to next device." << std::endl << std::endl;

            // Next
            continue;
        }

        // Allocate Memory For Device Name
        WCHAR* wcDeviceName = new WCHAR[nBufferSize + 1];

        // Got Memory
        if (wcDeviceName == NULL)
        {
            // Error
            std::cout << "ERR: Unable to allocate memory for Device Name.. Moving to next device." << std::endl << std::endl;

            // Next
            continue;
        }

        // Get Name
        nResult = GetRawInputDeviceInfo(pRawInputDeviceList[i].hDevice, // Device
            RIDI_DEVICENAME,                // Get Device Name
            wcDeviceName,                   // Get Name!
            &nBufferSize);                 // Char Count

                                           // Got Device Name?
        if (nResult < 0)
        {
            // Error
            std::cout << "ERR: Unable to get Device Name.. Moving to next device." << std::endl << std::endl;

            // Clean Up
            delete[] wcDeviceName;

            // Next
            continue;
        }

        // Set Device Info & Buffer Size
        RID_DEVICE_INFO rdiDeviceInfo;
        rdiDeviceInfo.cbSize = sizeof(RID_DEVICE_INFO);
        nBufferSize = rdiDeviceInfo.cbSize;

        // Get Device Info
        nResult = GetRawInputDeviceInfo(pRawInputDeviceList[i].hDevice,
            RIDI_DEVICEINFO,
            &rdiDeviceInfo,
            &nBufferSize);

        // Got All Buffer?
        if (nResult < 0)
        {
            // Error
            std::cout << "ERR: Unable to read Device Info.. Moving to next device." << std::endl << std::endl;

            // Next
            continue;
        }

        // Mouse
        if (rdiDeviceInfo.dwType == RIM_TYPEMOUSE)
        {
            // Current Device
            std::cout << std::endl << "Displaying device " << i + 1 << " information. (MOUSE)" << std::endl;
            std::wcout << L"Device Name: " << wcDeviceName << std::endl;
            std::cout << "Mouse ID: " << rdiDeviceInfo.mouse.dwId << std::endl;
            std::cout << "Mouse buttons: " << rdiDeviceInfo.mouse.dwNumberOfButtons << std::endl;
            std::cout << "Mouse sample rate (Data Points): " << rdiDeviceInfo.mouse.dwSampleRate << std::endl;
            if (rdiDeviceInfo.mouse.fHasHorizontalWheel)
            {
                std::cout << "Mouse has horizontal wheel" << std::endl;
            }
            else
            {
                std::cout << "Mouse does not have horizontal wheel" << std::endl;
            }
        }

        // Keyboard
        else if (rdiDeviceInfo.dwType == RIM_TYPEKEYBOARD)
        {
            // Current Device
           std::cout << std::endl << "Displaying device " << i + 1 << " information. (KEYBOARD)" << std::endl;
           std::wcout << L"Device Name: " << wcDeviceName << std::endl;
           std::cout << "Keyboard mode: " << rdiDeviceInfo.keyboard.dwKeyboardMode << std::endl;
           std::cout << "Number of function keys: " << rdiDeviceInfo.keyboard.dwNumberOfFunctionKeys << std::endl;
           std::cout << "Number of indicators: " << rdiDeviceInfo.keyboard.dwNumberOfIndicators << std::endl;
           std::cout << "Number of keys total: " << rdiDeviceInfo.keyboard.dwNumberOfKeysTotal << std::endl;
           std::cout << "Type of the keyboard: " << rdiDeviceInfo.keyboard.dwType << std::endl;
           std::cout << "Subtype of the keyboard: " << rdiDeviceInfo.keyboard.dwSubType << std::endl;
        }

        // Some HID
        else // (rdi.dwType == RIM_TYPEHID)
        {
            // Current Device
            std::cout << std::endl << "Displaying device " << i + 1 << " information. (HID)" << std::endl;
            std::wcout << L"Device Name: " << wcDeviceName << std::endl;
            std::cout << "Vendor Id:" << rdiDeviceInfo.hid.dwVendorId << std::endl;
            std::cout << "Product Id:" << rdiDeviceInfo.hid.dwProductId << std::endl;
            std::cout << "Version No:" << rdiDeviceInfo.hid.dwVersionNumber << std::endl;
            std::cout << "Usage for the device: " << rdiDeviceInfo.hid.usUsage << std::endl;
            std::cout << "Usage Page for the device: " << rdiDeviceInfo.hid.usUsagePage << std::endl;
        }

        // Delete Name Memory!
        delete[] wcDeviceName;
    }

    // Clean Up - Free Memory
    delete[] pRawInputDeviceList;

    // Exit
    std::cout << std::endl << "Finnished.";
    // cin.get();
    // return 0;
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


//-----------------------------------------------------------------------------
// // Name: EnumJoysticksCallback()
// // Desc: Called once for each enumerated joystick. If we find one, create a
// //       device interface on it so we can play with it.
// //-----------------------------------------------------------------------------
// BOOL CALLBACK EnumJoysticksCallback( const DIDEVICEINSTANCE* pdidInstance,
//                                      VOID* pContext )
// {
//     if( IsXInputDevice( &pdidInstance->guidProduct ) )
//         return DIENUM_CONTINUE;

//      // Device is verified not XInput, so add it to the list of DInput devices

//      return DIENUM_CONTINUE;
// }


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
        getinputdevices();
        DWORD dwResult;
        for (DWORD i=0; i< XUSER_MAX_COUNT; i++ )
        {
            XINPUT_STATE state;
            ZeroMemory( &state, sizeof(XINPUT_STATE) );

            // Simply get the state of the controller from XInput.
            dwResult = XInputGetState( i, &state );

            if( dwResult == ERROR_SUCCESS )
            {
                // Controller is connected
                std::cout << "controller connected !" << std::endl;
                primaryGamepadState = state;
    
                float LX = state.Gamepad.sThumbLX;
                float LY = state.Gamepad.sThumbLY;
                float RX = state.Gamepad.sThumbRX;
                float RY = state.Gamepad.sThumbRY;
                WORD  wButtons = state.Gamepad.wButtons;
                BYTE  bLeftTrigger = state.Gamepad.bLeftTrigger;
                BYTE  bRightTrigger = state.Gamepad.bRightTrigger;
            
                pLX = LX;
                pLY = LY;
                pRX = RX;
                pRY = RY;
                pwButtons = wButtons;
                pbLeftTrigger = bLeftTrigger;
                pbRightTrigger = bRightTrigger;

            }
            else
            {
                // Controller is not connected
                std::cout << "controller NOT connected !" << std::endl;
            }
        }

        // primaryGamepadState;
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
    
    XINPUT_STATE state;
    DWORD dwResult = XInputGetState(0, &state);
    float LX = state.Gamepad.sThumbLX;// / (32768.0f / 4.0f);
    float LY = state.Gamepad.sThumbLY;// / (32768.0f / 4.0f);
    float RX = state.Gamepad.sThumbRX;// / (32768.0f / 4.0f);
    float RY = state.Gamepad.sThumbRY;// / (32768.0f / 4.0f);
    WORD  wButtons = state.Gamepad.wButtons;
    BYTE  bLeftTrigger = state.Gamepad.bLeftTrigger;
    BYTE  bRightTrigger = state.Gamepad.bRightTrigger;
    // PXINPUT_KEYSTROKE pKeystroke;
    // XINPUT_KEYSTROKE* pKeystroke;
    // DWORD ret = XInputGetKeystroke(0, 0 , &pKeystroke);

    // std::cout << "LX:  " << LX << std::endl;
    // std::cout << "LY:  " << LY << std::endl;
    // std::cout << "RX:  " << RX << std::endl;
    // std::cout << "RY:  " << RY << std::endl;
    
    if (pLX != LX)
        std::cout << "LX:  " << LX << std::endl;
        
    if (pLY != LY)
        std::cout << "LY:  " << LY << std::endl;

    if (pRX != RX)
        std::cout << "RX:  " << RX << std::endl;
    
    if (pRY != RY)
        std::cout << "RY:  " << LY << std::endl;

    if (pwButtons != wButtons)
        std::cout << "wbuttons:  " << wButtons << std::endl;

    if (pbLeftTrigger != bLeftTrigger)
        std::cout << "bLeftTrigger:  " << bLeftTrigger << std::endl;
    
    if (pbRightTrigger != bRightTrigger)
        std::cout << "bRightTrigger:  " << bRightTrigger << std::endl;
    
    /**
     * xbox gamepad wbutton codes
     * A 4096
     * B 8192
     * X 16384
     * Y 32768
     * U 1
     * D 2
     * R 4
     * L 8
     * DL 6
     * DR 10
     * UL 8
     * UR 5
     * menu button 16
     * window button 32
     * LB 256
     * RB 512
     * L joystick click 64
     * R joystick click 128
     */
    /**
     * combos
     * A+B % A = 0
     * A+B % B = A
     * A+B+X % A = 0
     * A+B+X % B = A
     * A+B+X % X = A+B
     * 
     * U+L % U = 0
     * U+L % L = U
     */
    float gamepadSensitivity = 0.01f;
    float gamepadMovement = 1.0f * gamepadSensitivity;
    glm::vec3 position(0.0f, 0.0f, 0.0f);
    uint8_t controllerID = 0;
    // XINPUT_STATE state;
    XINPUT_VIBRATION vibration;

    if (wButtons & XINPUT_GAMEPAD_B)
    {
        bPressed = true;
    }
    else
    {                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
        bPressed = false;
    }
    
    if (bPressed == true)
    {
        // gamepad.Vibrate(20000, 20000);
        vibration.wLeftMotorSpeed = 20000;
        vibration.wRightMotorSpeed = 20000;
        XInputSetState(controllerID , &vibration);
    }
    else
    {
        // gamepad.resetVibration();
        vibration.wLeftMotorSpeed = 0;
        vibration.wRightMotorSpeed = 0;
        XInputSetState(controllerID , &vibration);
    }

    if (wButtons & XINPUT_GAMEPAD_Y)
    {
        std::cout << "object Z+" << std::endl;
        position.z += gamepadMovement;
    }
    
    if (wButtons & XINPUT_GAMEPAD_A)
    {
        std::cout << "object Z-" << std::endl;
        position.z -= gamepadMovement;
    }

    if (wButtons & XINPUT_GAMEPAD_DPAD_UP)
    {
        std::cout << "object Y+" << std::endl;
        position.y += gamepadMovement;
    }

    if (wButtons & XINPUT_GAMEPAD_DPAD_DOWN)
    {
        std::cout << "object Y-" << std::endl;
        position.y -= gamepadMovement;
    }
    
    if (wButtons & XINPUT_GAMEPAD_DPAD_LEFT)
    {
        std::cout << "object X+" << std::endl;
        position.x += gamepadMovement;
    }

    if (wButtons & XINPUT_GAMEPAD_DPAD_RIGHT)
    {
        std::cout << "object X-" << std::endl;
        position.x -= gamepadMovement;
    }

    if (position != glm::vec3(0.0f, 0.0f, 0.0f))
    {
        model->moveObject(position);
    }

    if (wButtons & XINPUT_GAMEPAD_LEFT_SHOULDER)
    {
        std::cout << "switching active object" << std::endl;
        currentActiveObjectIndex = model->switchActiveObject(1);
    }

    if (wButtons & XINPUT_GAMEPAD_RIGHT_SHOULDER)
    {
        std::cout << "switching active object" << std::endl;
        currentActiveObjectIndex = model->switchActiveObject(-1);
    }

    // std::cout << "currently active object: " << currentActiveObjectIndex << std::endl;

    // // check what buttons are currently pressed
    // uint16_t x = 0;
    // uint32_t pk = false;
    // for (uint8_t e = 15u; e >= 0 ; e--)
    // {
    //     x = pow(2, e);
    //     pk = (wButtons % x );
    //     // if ((wButtons % x )!= wButtons)
    //     // {
    //     //     pressedkey;
    //     // }
    // }

    // if (wButtons ==  9)
    // {
    //     std::cout << "object X+ Y+" << std::endl;
    //     model->moveObject(glm::vec3(gamepadMovement*gamepadSensitivity, gamepadMovement*gamepadSensitivity, 0.0));
    // }
    // if (wButtons ==  10)
    // {
    //         std::cout << "object X+ Y-" << std::endl;
    //         model->moveObject(glm::vec3(gamepadMovement*gamepadSensitivity, -gamepadMovement*gamepadSensitivity, 0.0));
    // }
    // if (wButtons ==  5)
    // {
    //         std::cout << "object X- Y+" << std::endl;
    //         model->moveObject(glm::vec3(-gamepadMovement*gamepadSensitivity, gamepadMovement*gamepadSensitivity, 0.0));
    // }
    // if (wButtons ==  6)
    // {
    //         std::cout << "object X- Y-" << std::endl;
    //         model->moveObject(glm::vec3(-gamepadMovement*gamepadSensitivity, -gamepadMovement*gamepadSensitivity, 0.0));
    // }
    //     if (wButtons ==  8)
    //     {
    //         std::cout << "object X+" << std::endl;
    //         model->moveObject(glm::vec3(gamepadMovement*gamepadSensitivity, 0.0, 0.0));
    //     }
    //     if (wButtons ==  1)
    //     {
    //          std::cout << "object Y+" << std::endl;
    //          model->moveObject(glm::vec3(0.0, gamepadMovement*gamepadSensitivity, 0.0));
    //     }
    //     if (wButtons ==  4)
    //     {
    //          std::cout << "object X-" << std::endl;
    //          model->moveObject(glm::vec3(-gamepadMovement*gamepadSensitivity, 0.0, 0.0));
    //     }
    //     if (wButtons ==  2)
    //     {
    //          std::cout << "object Y-" << std::endl;
    //          model->moveObject(glm::vec3(0.0, -gamepadMovement*gamepadSensitivity, 0.0));
    //     }
    //     if (wButtons ==  4096)
    //     {
    //          std::cout << "object Z+" << std::endl;
    //          model->moveObject(glm::vec3(0.0, 0.0, gamepadMovement*gamepadSensitivity));
    //     }
    //     if (wButtons ==  32768)
    //     {
    //          std::cout << "object Z-" << std::endl;
    //          model->moveObject(glm::vec3(0.0, 0.0, -gamepadMovement*gamepadSensitivity));
    //      }

    //  if (pwButtons != wButtons)
    //  {
    //      switch(wButtons)
    //      {
    //      case 4:
    //          std::cout << "object X+" << std::endl;
    //          model->moveObject(glm::vec3(1.0, 0.0, 0.0));
    //          break;
 
    //      case 1:
    //          std::cout << "object Y+" << std::endl;
    //          model->moveObject(glm::vec3(0.0, 1.0, 0.0));
    //          break;
 
    //      case 8:
    //          std::cout << "object X-" << std::endl;
    //          model->moveObject(glm::vec3(-1.0, 0.0, 0.0));
    //          break;
 
    //      case 2:
    //          std::cout << "object Y-" << std::endl;
    //          model->moveObject(glm::vec3(0.0, -1.0, 0.0));
    //          break;
 
    //      case 4096:
    //          std::cout << "object Z+" << std::endl;
    //          model->moveObject(glm::vec3(0.0, 0.0, 1.0));
    //          break;
 
    //      case 32768:
    //          std::cout << "object Z-" << std::endl;
    //          model->moveObject(glm::vec3(0.0, 0.0, -1.0));
    //          break;
    //      }
    //  }
 
    pwButtons = wButtons;
    pLX = LX;
    pLY = LY;
    pRX = RX;
    pRY = RY;
    pbLeftTrigger = bLeftTrigger;
    pbRightTrigger = bRightTrigger;

    // std::cout << "wbuttons:  " << state.Gamepad.wButtons << std::endl;
    // std::cout << "BLEFT TRIGGER:  " << state.Gamepad.bLeftTrigger << std::endl;
    // std::cout << "bright TRIGGER:  " << state.Gamepad.bRightTrigger << std::endl;
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
            model->switchActiveObject(1);
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
    // case WM_APPCOMMAND:
    // {
    //     int appCommand = GET_APPCOMMAND_LPARAM(lParam);
    //     switch (appCommand) {
    //         case APPCOMMAND_GAMEPAD_A:
    //             // Handle A button press
    //             break;
    //         case APPCOMMAND_GAMEPAD_B:
    //             // Handle B button press
    //             break;
    //         // ... handle other gamepad buttons
    //     }
    //     return 0;
    // }
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
        float cndcx = 2*(cposx / (windowRect.left - windowRect.right)) - 1;
        float cndcy = 2*(cposy / (windowRect.top - windowRect.bottom)) - 1;
        std::cout << "screen cursor position " << "x: " << cposx << " : y: "<< cposy << std::endl;
        std::cout << "NDC cursor position " << "x: " << cndcx << " : y: "<< cndcy << std::endl;
        model->handleCursor(cursorPosition.x - windowRect.left,  cursorPosition.y - windowRect.top);
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