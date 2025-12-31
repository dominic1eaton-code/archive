/**
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HCommon_h
#define HCommon_h

#include <string>

namespace hesabu
{

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

#endif // HCommon_h