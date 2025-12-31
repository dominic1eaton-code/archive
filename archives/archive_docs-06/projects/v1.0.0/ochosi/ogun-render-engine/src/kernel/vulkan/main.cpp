/**
 * @copyright
 * @brief
 * @note
 */

#include <iostream>
#include <chrono>
#include "ogun_app.h"

void test_vulkan_app()
{
    ogun::run_app();
}

int main()
{
    std::cout << "ogun renderer app" << std::endl;
    test_vulkan_app();
    return 0;
}