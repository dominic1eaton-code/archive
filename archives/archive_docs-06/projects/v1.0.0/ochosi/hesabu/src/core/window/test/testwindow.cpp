/**
 * @copyright
 * @brief: Test ApataDB application
 * @note : N/A
 * @reference:
 */

// #include "testwindowfixture.h"
#include <iostream>
#include <gtest/gtest.h>

/* Tests */
namespace hesabu::test
{

TEST(WindowTest, TestInput)
{
    int q = 1;
    EXPECT_TRUE(q == 1);
}
    
// /**
//  * Test Application creation
//  */
// TEST_F(TestWindowFixture, CanCreate)
// {
//     // std::string name = "Test Window";
//     // window->create(name);
//     int q = 1;
//     EXPECT_TRUE(q == 1);
// }

}; // namespace hesabu::test

int main(int argc, char **argv) 
{
    std::cout << "Running test suite" << std::endl;
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
