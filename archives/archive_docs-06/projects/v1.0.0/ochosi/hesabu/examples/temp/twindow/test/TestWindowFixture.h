/**
 * @copyright
 * @brief:
 * @note : N/A
 * @reference:
 */

#include "HWindow.h"
#include <iostream>
#include <gtest/gtest.h>

namespace hesabu::test
{

class TestWindowFixture : public testing::Test
{
    protected:
        // You can remove any or all of the following functions if its body
        // is empty.
    
        TestWindowFixture() {
            // You can do set-up work for each test here.
        }
    
        ~TestWindowFixture() override {
            // You can do clean-up work that doesn't throw exceptions here.
        }
    
        // If the constructor and destructor are not enough for setting up
        // and cleaning up each test, you can define the following methods:
        void SetUp() override {
            // Code here will be called immediately after the constructor (right
            // before each test).
            window = new HWindowWin32();
        }
    
        void TearDown() override {
            // Code here will be called immediately after each test (right
            // before the destructor).
        }

        /* Test Objects */
        HWindowWin32* window;
};

}; // namespace apata::test