/**
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HCursor_h
#define HCursor_h

#include <string>
#include "HCommon.h"

namespace hesabu
{

class HCursor
{
public:
    HCursor();
    ~HCursor();

private:
    
    HPoint m_position;

};

};

#endif // HCursor_h