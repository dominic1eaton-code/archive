/**
 * @copyright
 * @brief: Test ApataDB application
 * @note : N/A
 * @reference:
 */

#include "TestWindowFixture.h"
#include <iostream>

/* Tests */
namespace hesabu::test
{

/**
 * Test Application creation
 */
TEST_F(TestWindowFixture, CanCreate)
{
    std::string name = "Test Window";
    window->create(name);
    EXPECT_TRUE(window->status());
}

}; // namespace apata::test

int main(int argc, char **argv) 
{
    std::cout << "Running test suite" << std::endl;
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
