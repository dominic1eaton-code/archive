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

namespace ogun { class VulkanModel; }

namespace hesabu
{

class HWindow : public HBaseWindow<HWindow>
{
public:
    HWindow();
    virtual ~HWindow(void) = default;

    /**
     * @brief handle window message
     */
    LRESULT HandleMessage(UINT uMsg, WPARAM wParam, LPARAM lParam);

    /**
     * @brief initialize window
     */
    void init();

    /**
     * @brief update window
     */
    void update();

    /**
     * @brief draw window frame
     */
    void draw();
    
protected:
    float scrollPosition = 0.0f;

    double currentKeystate = 0;

   /**
     * @brief window has been resized?
     */
    bool bSize = false;

   /**
     * @brief handle key pressed
     */
    void handleKeyPress(WPARAM wParam);

    /**
     * @brief handle window been resized
     */
    void handleSize(UINT flag, uint32_t width, uint32_t height);

    /**
     * 
     */
    void handleScroll(double keystate, double scrollDelta, double xpos, double ypos);

    /**
     * @brief renderer model
     */
    ogun::VulkanModel* model;

   /**
     * @brief window has been initialized?
     */
    bool bInit = false;
};

} // namespace hesabu

#endif // HWindow_h