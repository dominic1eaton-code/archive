/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */
#pragma once

#include "Logger.h"
#include "gtest/gtest.h"

namespace LoggingTool
{

// The fixture for testing class Project1.
class TestLogger : public ::testing::Test
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
    Logger logger;
}

// Test logger can enable
TEST_F(TestLogger, CanEnable)
{
    logger->enable();
    EXPECT_TRUE(logger->enabled());
}

// Test logger can disable
TEST_F(TestLogger, CanDisable)
{
    logger->disable();
    EXPECT_FALSE(logger->enabled());
}

} //LoggingTool