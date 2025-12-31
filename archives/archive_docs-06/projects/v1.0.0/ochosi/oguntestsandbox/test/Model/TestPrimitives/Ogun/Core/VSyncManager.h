/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VSyncManager_h
#define VSyncManager_h

#include "VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VSyncManager : public VObject<VSyncManager>
{
public:
    VSyncManager(std::string rootPath);
    virtual ~VSyncManager(void) = default;

private:


};

} // namespace ogun

#endif // VSyncManager_h