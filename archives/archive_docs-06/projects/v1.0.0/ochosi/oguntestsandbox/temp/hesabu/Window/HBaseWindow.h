/**
 * @copyright
 * @brief
 * @note 
 */


#pragma once
#ifndef HBaseWindow_h
#define HBaseWindow_h

#ifdef PLAYFORM_WINDOWS
#include <windows.h>
#include <strsafe.h>
#pragma comment( lib, "user32.lib") 
#pragma comment( lib, "gdi32.lib")
#endif

#ifdef PLATFORM_UNIX
#   ifdef PLATFORM_X11
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#   endif
#   ifdef PLATFORM_WAYLAND
#   endif
#endif

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

#include <string>

namespace hesabu
{

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

class HBaseWindow
{
public:
    virtual void create() = 0;

    /**
     * return window name
     * @return window name
     */
    std::string name() const { return m_name; }

    /**
     * return window width
     * @return window width
     */
    uint16_t width() const { return m_width; }

    /**
     * return window height
     * @return window height
     */
    uint16_t height() const { return m_height; }

protected:

    std::string m_name;

    uint16_t m_width;

    uint16_t m_height;

    HWindowMode m_mode;

    const std::string DEFAULT_WINDOW_NAME = "hesabu window";
    
    const uint16_t DEFAULT_WIDTH = 600;

    const uint16_t DEFAULT_HEIGHT = 800;

};

class HBaseWindow_UNIX : public HBaseWindow
{
public:

    void create();


};
class HBaseWindow_WIN32 : public HBaseWindow
{
public:

    void create();

};

};

#endif // HBaseWindow_h