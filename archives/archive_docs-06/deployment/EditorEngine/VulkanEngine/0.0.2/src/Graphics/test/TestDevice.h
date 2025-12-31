/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 * @reference:
 *  https://github.com/dmonopoly/gtest-cmake-example
 *  https://github.com/google/googletest/tree/main/googletest/samples
 */
#pragma once

#include "Logger.h"
#include <gtest/gtest.h>
#include <iostream>

namespace TestVulkanEngine
{

class VInstance;
class PhysicalDevice;
class LogicalDevice;
class VWindow;

// The fixture for testing class Project1.
class TestLogger : public testing::Test
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

};

// Test vulkan instance creation
TEST_F(TestLogger, CreateInstance)
{
    VkApplicationInfo appInfo;
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "TestEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "TestEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    VInstance instance = new VInstance(m_appInfo);

    // cpre vulkan application instance created successfully
    EXPECT_TRUE(instance->created());
}

// Test VWindow creation
TEST_F(TestLogger, CreateVWindow)
{
    VWindow window = new VWindow(instance);

    // logical device created successfully
    EXPECT_TRUE(window->created());
}

// Test vulkan physical device creation
TEST_F(TestLogger, CreatePhysicalDevice)
{
    PhysicalDevice physicalDevice = new PhysicalDevice(instance);

    // An appropriate physical device was selected
    EXPECT_TRUE(physicalDevice->select());
}

// Test vulkan logical device creation
TEST_F(TestLogger, CreateLogicalDevice)
{
    LogicalDevice logicalDevice = new LogicalDevice(instance);

    // logical device created successfully
    EXPECT_TRUE(logicalDevice->created());
}

}

