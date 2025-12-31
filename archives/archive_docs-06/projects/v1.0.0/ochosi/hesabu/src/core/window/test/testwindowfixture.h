/**
 * @copyright
 * @brief:
 * @note : N/A
 * @reference:
 */

// #include "hesabu/hesabu.h"
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
    
        virtual ~TestWindowFixture() {
            // You can do clean-up work that doesn't throw exceptions here.
        }
    
        // If the constructor and destructor are not enough for setting up
        // and cleaning up each test, you can define the following methods:
        virtual void SetUp() {
            // Code here will be called immediately after the constructor (right
            // before each test).
            // window = new HWindowWin32();
        }
    
       virtual void TearDown() {
            // Code here will be called immediately after each test (right
            // before the destructor).
            // delete window;
        }

        /* Test Objects */
        // HWindowWin32* window;
};

}; // namespace hesabu::test