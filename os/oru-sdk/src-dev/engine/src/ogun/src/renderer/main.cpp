// temp test main 
#include <iostream>
#include "vulkan_renderer.h"

int main()
{
    std::cout << "running test main..." << std::endl;
    #ifdef NDEBUG
        printf("Release configuration!\n");
    #else
        printf("Debug configuration!\n");
    #endif

    ogun::init_renderer();

    return 0;
}