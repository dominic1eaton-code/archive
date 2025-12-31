/**
 * @copyright
 * @brief
 * @note
 */

#include <iostream>
#include "hesabu/hesabu.h"

struct Config
{
    hesabu::HPlatform platform;
};

int main()
{
    std::cout << "Running window example" << std::endl;
    Config config;
    config.platform = hesabu::HPlatform::WINDOWS;
    hesabu::HWindowWin32* window;
    if (config.platform == hesabu::HPlatform::WINDOWS)
    {
        window = new hesabu::HWindowWin32();
    }
    else if (config.platform == hesabu::HPlatform::UNIX)
    {
        // hesabu::HWindowUnix* window = new hesabu::HWindowUnix();
    }
    else
    {
        throw("undefined platform");
    }
    std::string default_window_name = "hesabu test window";
    window->create(default_window_name);
    window->show(hesabu::HWindowMode::HWS_NORMAL);
    window->poll();

    return 0;
}