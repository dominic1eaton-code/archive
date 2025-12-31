/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#include <iostream>
// #include <gtest/gtest.h>
#include "VInstance.h"

// /* Unit Test Fixtures */
// class TestDeviceFixture : public testing::Test
// {
// protected:
//     // You can remove any or all of the following functions if its body
//     // is empty.

//     TestDeviceFixture() {
//         // You can do set-up work for each test here.
//     }

//     virtual ~TestDeviceFixture() {
//         // You can do clean-up work that doesn't throw exceptions here.
//     }

//     // If the constructor and destructor are not enough for setting up
//     // and cleaning up each test, you can define the following methods:
//     virtual void SetUp() {
//         // Code here will be called immediately after the constructor (right
//         // before each test).
//     }

//     virtual void TearDown() {
//         // Code here will be called immediately after each test (right
//         // before the destructor).
//     }

//     // Objects declared here can be used by all tests in the test case for Project1.
//     RenderEngine::VInstance* m_instance;
// };

// /* Unit Tests */

// /* 
//  * @brief: Test vulkan instance initializes
//  */
// TEST_F(TestDeviceFixture, VinstanceInitializes)
// {
//     m_instance->initialize();
//     EXPECT_TRUE(true);
// }

// /* Unit Test Main */
// int main(int argc, char **argv) 
// {
//     std::cout << "Running test suite: Devices" << std::endl;
//     ::testing::InitGoogleTest(&argc, argv);
//     return RUN_ALL_TESTS();
// }

int main(int argc, char **argv) 
{
    // default application info from ENGINE
    VkApplicationInfo appInfo{};
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "RenderEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "RenderEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    RenderEngine::VInstance* m_instance = new RenderEngine::VInstance(appInfo);
    m_instance->create();
    return 0;
}
