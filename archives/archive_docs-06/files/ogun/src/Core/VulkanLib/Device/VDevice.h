/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VDevice_h
#define VDevice_h

#include "VObject.h"

namespace ogun
{

class VQueue
{
public:
    VQueue() = default;
    virtual ~VQueue(void) = default;
};

class VLogicallDevice
{
public:
    VLogicallDevice() = default;
    virtual ~VLogicallDevice(void) = default;
};

class VPhysicalDevice
{
public:
    VPhysicalDevice() = default;
    virtual ~VPhysicalDevice(void) = default;
};

class VDevice
{
public:
    VDevice() = default;
    virtual ~VDevice(void) = default;
};

} // namespace ogun

#endif // VDevice_h