/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */

#include <iostream>
#include <gtest/gtest.h>

int main(int argc, char** argv) 
{
    std::cout << "test project" << std::endl;
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
