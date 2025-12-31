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
    // hesabu::HWindowWin32* window = new hesabu::HWindowWin32();
    // hesabu::HWindowFactory* windowFactory;
    hesabu::HWindowWin32* window;
    if (config.platform == hesabu::HPlatform::WINDOWS)
    {
        // hesabu::HWindowFactoryWin32* windowFactory = new hesabu::HWindowFactoryWin32();
        window = new hesabu::HWindowWin32();
    }
    else if (config.platform == hesabu::HPlatform::UNIX)
    {
        // windowFactory = new hesabu::HWindowFactoryUnix();
        hesabu::HWindowUnix* window = new hesabu::HWindowUnix();
    }
    else
    {
        throw("undefined platform");
    }

    // hesabu::HBaseWindowWin32* window = dynamic_cast<hesabu::HBaseWindowWin32*>(windowFactory->createWindowWin32());
    window->show(0);

    return 0;
}