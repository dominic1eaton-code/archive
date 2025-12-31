/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef Kernel_h
#define Kernel_h

#include "VKernelModel.h"
#include "Component.h"

namespace ogun
{

class Kernel : public Component<Kernel>
{
public:
    Kernel() = default;

    virtual ~Kernel(void) = default;

    void initialize();

private:

    KernelModel* model;

};

} // namespace ogun

#endif // Kernel_h