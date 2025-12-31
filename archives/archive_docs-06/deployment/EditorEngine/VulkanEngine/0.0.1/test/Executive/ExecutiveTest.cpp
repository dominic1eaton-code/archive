/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#pragma once

#include "Engine.h"
#include <gtest/gtest.h>
#include <iostream>

namespace
{

class TestExecutive : public testing::Test
{
protected:
    // You can remove any or all of the following functions if its body
    // is empty.

    TestLogger() {
        // You can do set-up work for each test here.
    }

    virtual ~TestLogger() {
        // You can do clean-up work that doesn't throw exceptions here.
    }

    // If the constructor and destructor are not enough for setting up
    // and cleaning up each test, you can define the following methods:
    virtual void SetUp() {
        // Code here will be called immediately after the constructor (right
        // before each test).
    }

    virtual void TearDown() {
        // Code here will be called immediately after each test (right
        // before the destructor).
    }

    // Objects declared here can be used by all tests in the test case for Project1.
   Engine engine;
};

// Test engine cycle
TEST_F(TestExecutive, CanCycle)
{
    engine.cycleMode(EngineMode::CONFIGURE);
    EXPECT_TRUE(engine.mode());

    engine.cycleMode(EngineMode::INITIALIZE);
    EXPECT_TRUE(engine.mode());

    engine.cycleMode(EngineMode::UPDATE);
    EXPECT_TRUE(engine.mode());

    engine.cycleMode(EngineMode::PAUSE);
    EXPECT_TRUE(engine.mode());

    engine.cycleMode(EngineMode::SHUTDOWN);
    EXPECT_TRUE(engine.mode());
}

}

int main(int argc, char **argv) 
{
    std::cout << "Running test suite" << std::endl;
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
