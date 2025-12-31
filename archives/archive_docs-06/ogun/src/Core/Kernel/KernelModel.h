/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef KernelModel_h
#define KernelModel_h

namespace ogun
{

class KernelModel
{
public:
    KernelModel() = default;

    virtual ~KernelModel(void) = default;

    virtual void init() = 0;

    virtual void run() = 0;

    virtual void shutdown() = 0;
};

} // namespace ogun

#endif // KernelModel_h