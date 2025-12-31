/**
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HWindow_h
#define HWindow_h

#include <memory>
#include <windows.h>

namespace hesabu
{

enum class HWindowEvent
{
    HEVENT_MOUSE = 0u,
    HEVENT_KEYBOARD =1u,
    HEVENT_SCREEN =2u
};

/* public interfaces */
template<class DERIVED_TYPE>
class IHBaseWindowUnix
{
    class HBaseWindowUnix;
    // HBaseWindowUnix* pImpl;
    std::unique_ptr<HBaseWindowUnix> pimpl;
};

template<class DERIVED_TYPE>
class IHBaseWindowWin32
{
public:
    IHBaseWindowWin32();
    ~IHBaseWindowWin32();

private:
    template<class DERIVED_TYPE>
    class HBaseWindowWin32;
    HBaseWindowWin32<DERIVED_TYPE>* pImpl;
    // std::unique_ptr<HBaseWindowWin32<DERIVED_TYPE>> pimpl;
};

/* public classes */
class HWindowUnix : public IHBaseWindowUnix<HWindowUnix>
{
public:
    HWindowUnix() = default;
    virtual ~HWindowUnix() = default;

};

class HWindowWin32 : public IHBaseWindowWin32<HWindowWin32>
{
public:
    HWindowWin32() = default;
    virtual ~HWindowWin32() = default;

    /**
     * handle window message
     * @param uMsg
     * @param wParam
     * @param lParam
     */
    LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam);

    /**
     * handle key event
     */
    void handleKeyEvent();

    /**
     * handle cursor event
     */
    void handleCursorEvent();

    /**
     * handle mouse event
     */
    void handleMouseEvent();

    /**
     * handle scroll event
     */
    void handleScrollEvent() ;

    /**
     * handle screen event
     */
    void handleScreenEvent();
};

};

#endif // HWindow_h