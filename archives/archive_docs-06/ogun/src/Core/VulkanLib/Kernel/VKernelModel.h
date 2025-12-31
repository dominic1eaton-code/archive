/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VKernelModel_h
#define VKernelModel_h

#include "KernelModel.h"

namespace ogun
{

class VKernelModel : public KernelModel
{
public:
    VKernelModel() = default;
    virtual ~VKernelModel(void) = default;

    void init();

    void run();

    void shutdown();
};

} // namespace ogun

#endif // VKernelModel_h