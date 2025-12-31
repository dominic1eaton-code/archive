/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VWindow_h
#define VWindow_h

#include "VObject.h"

namespace ogun
{

class VSurface
{
public:
    VSurface() = default;
    virtual ~VSurface(void) = default;
};

class VWindow
{
public:
    VWindow() = default;
    virtual ~VWindow(void) = default;
};

} // namespace ogun

#endif // VWindow_h