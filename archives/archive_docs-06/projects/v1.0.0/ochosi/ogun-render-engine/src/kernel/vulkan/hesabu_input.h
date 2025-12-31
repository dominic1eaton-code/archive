


#include <functional>
#include <array>


namespace hesabu
{
enum class HKey
{
    HKEY_A
};


void add_input();
void add_keyboard();
void add_gamepad();
void add_mouse();
void add_screen();

template<typename T, typename ...Args>
void add_keybinding(HKey key, std::function<T(Args...)> func)
{

}


};