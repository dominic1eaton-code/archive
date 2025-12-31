
void runWindowManager()
{
    ogunWindowCreateMessageData data;
    data.name = "OgunEngine";
    std::wstring widestr = std::wstring(data.name.begin(), data.name.end());
    hesabu::HWindow* window = new hesabu::HWindow();
    window->create(widestr.c_str());
    window->show();
    // LPDWORD lpdwProcessId = 0;
    // DWORD id = GetWindowThreadProcessId( window->hwnd(), lpdwProcessId );
    window->message();
}

// Callback function that handles events.
void CALLBACK HandleWinEvent(HWINEVENTHOOK hook, DWORD event, HWND hwnd, 
  LONG idObject, LONG idChild, 
  DWORD dwEventThread, DWORD dwmsEventTime)
{
    std::cout << "Got event " << event << '\n' << std::flush;
}


// LRESULT CALLBACK hook_proc( int code, WPARAM wParam, LPARAM lParam )
// {
//   static long ctrl_cnt = 0;
//   static bool mmode = false;
//   static DWORD time;

//   KBDLLHOOKSTRUCT*  kbd = (KBDLLHOOKSTRUCT*)lParam;

//   if (  code < 0
//   ||   (kbd->flags & 0x10) // ignore injected events
//      ) return CallNextHookEx( thehook, code, wParam, lParam );

//   long ret = 1; // by default I swallow the keys
//   if (  mmode  ) { // macro mode is ON
//     if (  WM_KEYDOWN == wParam  )
//       PostMessage(mainwnd, WM_MCR_ACCUM, kbd->vkCode, 0);

//     if (  WM_KEYUP == wParam  )
//       switch (kbd->vkCode) {
//         case VK_ESCAPE:
//           mmode = false;
//           keys.removeall();
//           PostMessage(mainwnd, WM_MCR_HIDE, 0, 0);
//           break;

//         case VK_RETURN:
//           PostMessage(mainwnd, WM_MCR_EXEC, 0, 0);
//           break;

//         case VK_LCONTROL:
//           mmode = false;
//           PostMessage(mainwnd, WM_MCR_HIDE, 0, 0);
//           PostMessage(mainwnd, WM_MCR_EXEC, 0, 0);
//           break;
//       }

//     /* Which non printable keys allow passing? */
//     switch( kbd->vkCode ) {
//       case VK_LCONTROL:
//       case VK_CAPITAL:
//       case VK_LSHIFT:
//       case VK_RSHIFT:
//         ret = CallNextHookEx( thehook, code, wParam, lParam );
//     }
//   }
//   else { // macro mode is OFF
//     /* Ctrl pressed */
//     if (  kbd->vkCode == VK_LCONTROL && WM_KEYDOWN == wParam  ) {
//       ctrl_cnt = 1;
//       time = kbd->time;
//     }

//     /* Prevent ctrl combinations to activate macro mode */
//     if (  kbd->vkCode != VK_LCONTROL  )
//       ctrl_cnt = 0;

//     /* Ctrl released */
//     if (  ctrl_cnt == 1 && WM_KEYUP == wParam  ) {
//       if (  kbd->time - time > 40  ) {
//         mmode = true;
//         PostMessage(mainwnd, WM_MCR_SHOW, 0, 0);
//       }
//     }

//     ret = CallNextHookEx( thehook, code, wParam, lParam ); // let it pass
//   }

//   return ret;
// }


LRESULT CALLBACK LowLevelKeyboardProc(int nCode, WPARAM wParam, LPARAM lParam) {
    if (nCode == HC_ACTION) {
        PKBDLLHOOKSTRUCT p = (PKBDLLHOOKSTRUCT)lParam;
        if (wParam == WM_KEYDOWN || wParam == WM_SYSKEYDOWN) {
            // Process the key event, p->vkCode contains the virtual-key code
            std::cout << p->vkCode << std::endl;
        }
    }
    return CallNextHookEx(NULL, nCode, wParam, lParam);
}



/**
 * @header
 * @copyright
 * @brief
 * @note
 */
#include <iostream>
#include <unordered_map>
#include <map>
#include <string>
#include <queue>
#include <vector>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <chrono>
#include <winsock2.h>
#include <array>
#include <stdexcept>

#include "Modules/Hesabu/Window/HWindow.h"

struct ogunWindowCreateMessageData
{
    ogunWindowCreateMessageData()
        : name("")
        , width(600)
        , height(800)
        , mode(hesabu::HWindowMode::NORMAL)
    {}

    std::string name;

    uint32_t width;

    uint32_t height;

    hesabu::HWindowMode mode;
};

void runVulkanModel()
{
    // temp receive message time delay simulate
    std::this_thread::sleep_for(std::chrono::seconds(2));
    ogunWindowCreateMessageData data;
 
    data.name = "hesabu window";
    HWND hwnd = FindWindow(data.name.c_str(), 0);
    MSG msg = {0};
    
    LPDWORD lpdwProcessId = 0;
    DWORD id = GetWindowThreadProcessId( hwnd, lpdwProcessId );
    // HWINEVENTHOOK thehook = SetWindowsHookEx( WH_KEYBOARD_LL, hook_proc, hwnd, 0 );

    // EVENT_SYSTEM_MENUSTART; 
    // HWINEVENTHOOK g_hook = SetWinEventHook(
    // EVENT_MIN , EVENT_MAX,  // Range of events.
    // NULL,                   // Handle to DLL.
    // HandleWinEvent,         // The callback.
    // 0, 0,                   // Process and thread IDs of interest (0 = all)
    // WINEVENT_OUTOFCONTEXT | WINEVENT_SKIPOWNPROCESS); // Flags.


    // HHOOK hHook = SetWindowsHookEx(WH_KEYBOARD_LL, LowLevelKeyboardProc, GetModuleHandle(NULL), 0);
    // HHOOK hHook = SetWindowsHookExW(WH_KEYBOARD_LL, LowLevelKeyboardProc, NULL, 0);
    // MessageBoxW(NULL, L"hooking", L"", MB_ICONEXCLAMATION | MB_SYSTEMMODAL);

    // HWND hwnd;
    // BOOL fDone;
    // MSG msg;
    
    // Begin the operation and continue until it is complete 
    // or until the user clicks the mouse or presses a key. 
    
    // fDone = FALSE;
    // BOOL b;
    // while (!fDone) 
    // { 
    //     // fDone = DoLengthyOperation(); // application-defined function 
    
    //     // Remove any messages that may be in the queue. If the 
    //     // queue contains any mouse or keyboard 
    //     // messages, end the operation. 
    //     LPARAM lParam = 0x29A1; //The hexadecimal value matching with the parameters you want* example . 
    //     WPARAM wParam = VK_SPACE;
    //     PostMessage(HWND_BROADCAST, WM_KEYDOWN, wParam, lParam); 
    //     PostMessage(hwnd, WM_KEYDOWN, wParam, lParam); 

    //       while (b = PeekMessage(&msg, hwnd,  0, 0, PM_REMOVE)) 
    //     { 
    //         switch(msg.message) 
    //         { 
    //             case WM_LBUTTONDOWN: 
    //             case WM_RBUTTONDOWN: 
    //             case WM_KEYDOWN: 
    //                 // 
    //                 // Perform any required cleanup. 
    //                 // 
    //                 fDone = TRUE; 
    //         } 
    //     } 
    // } 

    // MSG msg;
    // while (GetMessage(&msg, NULL, 0, 0))
    // {
    //     TranslateMessage(&msg);
    //     DispatchMessage(&msg);
    // }

    // UnhookWindowsHookEx(hHook);
    // UnhookWinEvent(g_hook);

    // HWINEVENTHOOK SetWinEventHook(
    //     [in] DWORD        eventMin,
    //     [in] DWORD        eventMax,
    //     [in] HMODULE      hmodWinEventProc,
    //     [in] WINEVENTPROC pfnWinEventProc,
    //     [in] DWORD        idProcess,
    //     [in] DWORD        idThread,
    //     [in] DWORD        dwFlags
    // );


    // while (msg.message != WM_QUIT)
    // {
    //     //default message processing
    //     // if (PeekMessage(&msg, hwnd, 0, 0, PM_REMOVE))
    //     if (GetMessage(&msg, hwnd, 0, 0))
    //     {
    //         TranslateMessage(&msg);
    //         DispatchMessage(&msg);
    //     }
    //     else 
    //     { 
    //         //constantly paint the window when there is no other message
    //         // render_window(hwnd);
    //     }
    // }

    // while(1)
    // {
    //     while (PeekMessage(&msg,	hwnd,	0,	0)	>	0)	
    //     {	
    //         TranslateMessage(&msg);	
    //         msg.message;
    //         // DispatchMessage(&msg);	

    //     }
    // }

}

void runVulkan()
{
    ogunWindowCreateMessageData data;
    data.name = "OgunEngine";
    std::wstring widestr = std::wstring(data.name.begin(), data.name.end());
    hesabu::HWindow* window = new hesabu::HWindow();
    window->create(widestr.c_str());
    window->init();
    window->show();
    window->message();
}

void testModel()
{
    // std::cout << "run test kernel model" << std::endl;
    // std::thread windowManagerThread(runWindowManager);
    // std::thread vulkanModelThread(runVulkanModel);
    // windowManagerThread.join();
    // vulkanModelThread.join();
    runVulkan();
}

int main(int argc, char* argv[])
{
    testModel();
    std::cout << " test kernel " << std::endl;
    return 0;
}
