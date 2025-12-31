/**
 * @brief
 * @note
 * @reference 
 *    https://hereket.com/posts/linux_creating_x11_windows/
 */

#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <stdio.h>
#include <iostream>
#include <cstdlib> // Required for system()

void testWindow0()
{
    Display* MainDisplay = XOpenDisplay(0);
    Window RootWindow = XDefaultRootWindow(MainDisplay);
    
    if (MainDisplay == NULL) {
        fprintf(stderr, "Cannot open display\n");
        exit(1);
    }

    int WindowX = 0;
    int WindowY = 0;
    int WindowWidth = 800;
    int WindowHeight = 600;
    int BorderWidth = 0;
    int WindowDepth = CopyFromParent;
    int WindowClass = CopyFromParent;
    Visual* WindowVisual = CopyFromParent;

    int AttributeValueMask = CWBackPixel;
    XSetWindowAttributes WindowAttributes = {};
    WindowAttributes.background_pixel = 0xffafe9af;

    Window MainWindow = XCreateWindow(MainDisplay, RootWindow, 
            WindowX, WindowY, WindowWidth, WindowHeight,
            BorderWidth, WindowDepth, WindowClass, WindowVisual,
            AttributeValueMask, &WindowAttributes);

    XMapWindow(MainDisplay, MainWindow);
    std::cout << "Press Enter to continue...";
    std::cin.get();

    for(;;) {
        XEvent GeneralEvent = {};
        XNextEvent(MainDisplay, &GeneralEvent);
    }
}

void testWindow1()
{
    Display* MainDisplay = XOpenDisplay(0);
    Window RootWindow = XDefaultRootWindow(MainDisplay);

    int WindowX = 0;
    int WindowY = 0;
    int WindowWidth = 800;
    int WindowHeight = 600;
    int BorderWidth = 0;
    int WindowDepth = CopyFromParent;
    int WindowClass = CopyFromParent;
    Visual* WindowVisual = CopyFromParent;

    int AttributeValueMask = CWBackPixel;
    XSetWindowAttributes WindowAttributes = {};
    WindowAttributes.background_pixel = 0xffafe9af;

    Window MainWindow = XCreateWindow(MainDisplay, RootWindow, 
            WindowX, WindowY, WindowWidth, WindowHeight,
            BorderWidth, WindowDepth, WindowClass, WindowVisual,
            AttributeValueMask, &WindowAttributes);

    XMapWindow(MainDisplay, MainWindow);
    std::cout << "Press Enter to continue...";
    std::cin.get();

    for(;;) {
        XEvent GeneralEvent = {};
        XNextEvent(MainDisplay, &GeneralEvent);
    }
}

typedef struct {
  int X;
  int Y;
  int Width;
  int Height;
} entity;

void testWindow2()
{
    Display* MainDisplay = XOpenDisplay(0);
    Window RootWindow = XDefaultRootWindow(MainDisplay);

    int DefaultScreen = DefaultScreen(MainDisplay);
    GC Context = XDefaultGC(MainDisplay, DefaultScreen);

    int WindowX = 0;
    int WindowY = 0;
    int WindowWidth = 800;
    int WindowHeight = 600;
    int BorderWidth = 0;
    int WindowDepth = CopyFromParent;
    int WindowClass = CopyFromParent;
    Visual* WindowVisual = CopyFromParent;

    int AttributeValueMask = CWBackPixel | CWEventMask;
    XSetWindowAttributes WindowAttributes = {};
    WindowAttributes.background_pixel = 0xffffccaa;
    WindowAttributes.event_mask = StructureNotifyMask | KeyPressMask | KeyReleaseMask | ExposureMask;

    Window MainWindow = XCreateWindow(MainDisplay, RootWindow, 
            WindowX, WindowY, WindowWidth, WindowHeight,
            BorderWidth, WindowDepth, WindowClass, WindowVisual,
            AttributeValueMask, &WindowAttributes);

    XMapWindow(MainDisplay, MainWindow);
    // std::cout << "1 Press Enter to continue...";
    // std::cin.get();

    XStoreName(MainDisplay, MainWindow, "Moving rectangle. Use arrow keys to move.");

    Atom WM_DELETE_WINDOW = XInternAtom(MainDisplay, "WM_DELETE_WINDOW", False);
    if(!XSetWMProtocols(MainDisplay, MainWindow, &WM_DELETE_WINDOW, 1)) {
        printf("Couldn't register WM_DELETE_WINDOW property \n");
    }

    std::cout << "2 Press Enter to continue...";
    std::cin.get();

    entity Box = {};
    Box.Width = 50;
    Box.Height = 80;
    Box.X = WindowWidth/2 - Box.Width/2;
    Box.Y = WindowHeight/2 - Box.Height/2;
    int StepSize = 5;

    int IsWindowOpen = 1;
    while(IsWindowOpen) {
        XEvent GeneralEvent = {};

        XNextEvent(MainDisplay, &GeneralEvent);
        // std::cout << "3 Press Enter to continue...";
        std::cin.get();

        switch(GeneralEvent.type) {
            case KeyPress:
            case KeyRelease:
            {
                XKeyPressedEvent *Event = (XKeyPressedEvent *)&GeneralEvent;
                if(Event->keycode == XKeysymToKeycode(MainDisplay, XK_Escape))
                {
                    IsWindowOpen = 0;
                }

                if(Event->keycode == XKeysymToKeycode(MainDisplay, XK_Down))
                {
                    Box.Y += StepSize;
                }
                else if(Event->keycode == XKeysymToKeycode(MainDisplay, XK_Up))
                {
                    Box.Y -= StepSize;
                }
                else if(Event->keycode == XKeysymToKeycode(MainDisplay, XK_Right))
                {
                    Box.X += StepSize;
                }
                else if(Event->keycode == XKeysymToKeycode(MainDisplay, XK_Left))
                {
                    Box.X -= StepSize;
                }
            } break;

            case ClientMessage:
            {
                XClientMessageEvent *Event = (XClientMessageEvent *) &GeneralEvent;
                if((Atom)Event->data.l[0] == WM_DELETE_WINDOW) {
                    XDestroyWindow(MainDisplay, MainWindow);
                    IsWindowOpen = 0;
                }
            } break;

        }

        XClearWindow(MainDisplay, MainWindow);
        XFillRectangle(MainDisplay, MainWindow, Context, Box.X, Box.Y, Box.Width, Box.Height);
    }
}

int main()
{
    // testWindow0();
    // testWindow1();
    testWindow2();
    return 0;
}

// int main() {
//   Display* display = XOpenDisplay(nullptr);
//   if (display == nullptr) {
//     std::cerr << "Cannot open display" << std::endl;
//     return -1;
//   }

//   int screen = DefaultScreen(display);
//   Window window = XCreateSimpleWindow(display, RootWindow(display, screen), 10, 10, 400, 300, 1,
//                                      BlackPixel(display, screen), WhitePixel(display, screen));
//   XMapWindow(display, window);
//   XFlush(display);

//   XEvent event;
//   while (true) {
//     XNextEvent(display, &event);
//     if (event.type == Expose) {
//       // Handle window redrawing if needed
//     }
//   }

//   XCloseDisplay(display);
//   return 0;
// }
