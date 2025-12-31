/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef HKeyboard_h
#define HKeyboard_h

#include "HInput.h"
#include <vector>

namespace ogun
{
    
/**
 * @brief key input mode
 */
enum class KeyMode
{
    K_KEY_DOWN,
    K_KEY_UP,
    K_KEY_HOLD,
    K_KEY_FIRST
};

/**
 * @brief key type
 */
enum class Keys
{
    K_ESC,
    K_F1,
    K_F2,
    K_F3,
    K_F4,
    K_F5,
    K_F6,
    K_F7,
    K_F8,
    K_F9,
    K_F10,
    K_F11,
    K_F12,
    K_INSERT,
    K_DELETE,

    K_BACKQUOTE,
    K_1,
    K_2,
    K_3,
    K_4,
    K_5,
    K_6,
    K_7,
    K_8,
    K_9,
    K_0,
    K_MINUS,
    K_EQUAL,
    K_BACKSPACE,

    K_TAB,
    K_CAPSLOCK,
    K_LEFT_SHIFT,
    K_RIGHT_SHIFT,
    K_FN,
    K_WINDOWS,
    K_LEFT_ALT,
    K_RIGHT_ALT,
    K_SPACEBAR,
    K_LEFT_CTRL,
    K_RIGHT_CTRL,
    K_PAGEUP,
    K_PAGEDOWN,
    K_UP,
    K_DOWN,
    K_LEFT,
    K_RIGHT,
    K_ENTER,
    K_LEFT_BRACKET,
    K_RIGHT_BRACKET,
    K_BACKSLASH,
    K_QUESTIONMARK,
    K_SEMICOLON,
    K_QUOTE,
    K_COMMA,
    K_PERIOD,

    K_A,
    K_B,
    K_C,
    K_D,
    K_E,
    K_F,
    K_G,
    K_H,
    K_I,
    K_J,
    K_K,
    K_L,
    K_M,
    K_N,
    K_O,
    K_P,
    K_Q,
    K_R,
    K_S,
    K_T,
    K_U,
    K_V,
    K_W,
    K_X,
    K_Y,
    K_Z,

    K_POWER,
    K_CALCULATOR,
    K_CLEAR,
    K_PLUSMINuS,

    K_FORWARDSLASH,
    K_NUM_FORWARDSLASH,
    K_NUMLOCK,
    K_ASTERISK,
    K_MINUS,
    K_PLUS,
    K_NUM_ENTER,
    K_NUM_PERIOD,
    K_NUM_0,
    K_NUM_1,
    K_NUM_2,
    K_NUM_3,
    K_NUM_4,
    K_NUM_5,
    K_NUM_6,
    K_NUM_7,
    K_NUM_8,
    K_NUM_9,
};

template<class U>
class HKeyboard : public HInput<HKeyboard>
{
public:
    HKeyboard();
    virtual ~HKeyboard(void) = default;

private:

};

} // namespace ogun

#endif // HKeyboard_h