/**
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef hstructures_h
#define hstructures_h

#include <string>

namespace hesabu
{

enum class HPlatform
{
    WINDOWS,
    UNIX,
    ANDROID,
    IOS
};

enum class HWindowPlatform
{
    WIN_32,
    X11,
    WAYLAND,
    ANDROID,
    IOS
};

struct HExtent
{
    HExtent()
    {}

    HExtent(uint16_t w, uint16_t h)
        : width(w)
        , height(h)
    {}

    uint16_t width;

    uint16_t height;
};

struct HPoint
{
    HPoint()
    {}

    HPoint(uint16_t px, uint16_t py)
        : x(px)
        , y(py)
    {}

    uint16_t x;

    uint16_t y;
};

};

#endif // hstructures_h