/**
 * @header
 * @copyright
 * @brief
 * @note 
 */


#pragma once
#ifndef HWindow_h
#define HWindow_h

#include "HBaseWindow.h"
#include <string>

namespace hesabu
{

class HWindow : public HBaseWindow<HWindow>
{
public:
    HWindow() = default;
    virtual ~HWindow(void) = default;

    uint32_t create();
    
    LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam);

protected:

    void handleSize(UINT flag, int width, int height);

};

} // namespace hesabu

#endif // HWindow_h