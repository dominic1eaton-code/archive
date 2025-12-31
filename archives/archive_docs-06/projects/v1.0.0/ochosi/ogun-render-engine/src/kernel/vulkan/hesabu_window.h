/**
 * @copyright
 * @brief
 * @note
 */

#pragma once
#ifndef hesabu_window_h
#define hesabu_window_h

// #ifdef PLATFORM_WINDOWS
#include <windows.h>
#include <Xinput.h>
#include <wbemidl.h>
#include <oleauto.h>
#include <string>
#include <strsafe.h>
#pragma comment( lib, "user32.lib") 
#pragma comment( lib, "gdi32.lib")
// #endif // PLATFORM_WINDOWS

namespace hesabu
{

struct HWindowState
{
    PCWSTR lpWindowName = L"hesabu";
    DWORD dwStyle = WS_OVERLAPPEDWINDOW;
    DWORD dwExStyle = 0;
    int x = CW_USEDEFAULT;
    int y = CW_USEDEFAULT;
    unsigned int nWidth = 800;
    unsigned int nHeight = 600;
    HWND hWndParent = 0;
    HMENU hMenu = 0;
    HINSTANCE hInstance = GetModuleHandle(NULL);
    LPVOID lpParam = NULL;
    bool binit = false;
};

inline HWindowState* get_window_state(HWND hwnd)
{
    LONG_PTR ptr = GetWindowLongPtr(hwnd, GWLP_USERDATA);
    HWindowState *pState = reinterpret_cast<HWindowState*>(ptr);
    return pState;
}


void run_app();
void init_window(HWND& hwnd, uint32_t& width, uint32_t& height);
void poll_window();
void message_window();
BOOL create_window(HWindowState window, HWND& hwnd);
static LRESULT CALLBACK HWindowProc(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam);
static LRESULT handle_window_message(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam);
void draw_frame();
void cleanup_window();

void handle_keyboard();
void handle_mouse(WPARAM wParam, LPARAM lParam);
void handle_gamepad();

void handle_key_press(WPARAM wParam);
void handle_cursor(double xpos, double ypos);
void handle_scroll(double keystate, double scrollDelta, double xpos, double ypos);
void handle_resize(UINT flag, uint32_t width, uint32_t height);

}; // namespace hesabu

#endif // hesabu_window_h