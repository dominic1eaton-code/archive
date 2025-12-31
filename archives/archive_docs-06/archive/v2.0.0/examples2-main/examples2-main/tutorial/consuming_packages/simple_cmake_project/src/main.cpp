#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <iostream>
#include <zlib.h>
#include <Eigen/Dense>
#include <glm/glm.hpp>
#include <vulkan/vulkan.h>
#include <vector>

#ifdef NDEBUG
    #undef NDEBUG // Ensure NDEBUG is not defined
#endif
#include <cassert>

void test_zlib()
{
    std::cout << "running EIGEN test" << std::endl;
    /* testing ZLIB */
    char buffer_in [256] = {"Conan is a MIT-licensed, Open Source package manager for C and C++ development, "
                            "allowing development teams to easily and efficiently manage their packages and "
                            "dependencies across platforms and build systems."};
    char buffer_out [256] = {0};

    z_stream defstream;
    defstream.zalloc = Z_NULL;
    defstream.zfree = Z_NULL;
    defstream.opaque = Z_NULL;
    defstream.avail_in = (uInt) strlen(buffer_in);
    defstream.next_in = (Bytef *) buffer_in;
    defstream.avail_out = (uInt) sizeof(buffer_out);
    defstream.next_out = (Bytef *) buffer_out;

    deflateInit(&defstream, Z_BEST_COMPRESSION);
    deflate(&defstream, Z_FINISH);
    deflateEnd(&defstream);

    printf("Uncompressed size is: %lu\n", strlen(buffer_in));
    printf("Compressed size is: %lu\n", defstream.total_out);

    printf("ZLIB VERSION: %s\n", zlibVersion());
    std::cout << std::endl;
}

void test_eigen()
{
    std::cout << "running EIGEN test" << std::endl;
    /* testing EIGEN */
    // Declare a 3x3 matrix of floats
    Eigen::Matrix3f m;
    // Initialize the matrix using a comma initializer
    m << 1, 2, 3,
         4, 5, 6,
         7, 8, 9;

    // Declare a 3D vector of floats
    Eigen::Vector3f v(1, 2, 3);

    // Perform matrix-vector multiplication and print the result
    Eigen::Vector3f result = m * v;
    std::cout << "m * v =" << std::endl << result << std::endl;

    // Perform vector addition
    Eigen::Vector3f v2(4, 5, 6);

    std::cout << "v + v2 =" << std::endl << v + v2 << std::endl;
    std::cout << std::endl;
}

void test_glm()
{
    std::cout << "running GLM test" << std::endl;
    /* testing GLM */
    glm::vec4 Position = glm::vec4(glm::vec3(0.0), 1.0);
    glm::mat4 Model = glm::mat4(1.0);
    Model[4] = glm::vec4(1.0, 1.0, 0.0, 1.0);
    glm::vec4 Transformed = Model * Position;
    std::cout << "Transformed =" << std::endl
        << Transformed.x << " "
        << Transformed.y << " "
        << Transformed.z << " "
        << Transformed.w << " "
        << std::endl;
    std::cout << std::endl;
}

void test_vulkan()
{
    std::cout << "running VULKAN test" << std::endl;

    std::vector<const char*> m_extensions = {"VK_KHR_surface", "VK_KHR_win32_surface", "VK_EXT_debug_utils"};
    std::vector<const char*> m_layers = {"VK_LAYER_KHRONOS_validation"};
    VkInstance m_instance;
    VkApplicationInfo m_info;
    m_info.pNext = NULL;
    m_info.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    m_info.pApplicationName = "TestOgunEngine";
    m_info.applicationVersion = VK_MAKE_VERSION(1, 1, 0);
    m_info.pEngineName = "TestOgunEngine";
    m_info.engineVersion = VK_MAKE_VERSION(1, 1, 0);
    m_info.apiVersion = VK_MAKE_API_VERSION(0, 1, 1, 0);

    VkInstanceCreateInfo m_createInfo;
    m_createInfo.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
    m_createInfo.pNext = NULL;
    m_createInfo.flags = 0;
    m_createInfo.pApplicationInfo = &m_info;
    m_createInfo.enabledExtensionCount = m_extensions.size();
    m_createInfo.ppEnabledExtensionNames = m_extensions.data();
    m_createInfo.enabledLayerCount = m_layers.size();
    m_createInfo.ppEnabledLayerNames = m_layers.data();
    VkResult result = vkCreateInstance(
        &m_createInfo,
        nullptr,
        &m_instance);
    assert(result == VK_SUCCESS);
    std::cout << "vulkan object status : " << result << std::endl;

    // char* string = NULL;
    // // Assert that the pointer is not NULL
    // assert(string != NULL && "String pointer cannot be NULL"); 
    // // The rest of the function assumes 'string' is a valid pointer
    // std::cout << "Analyzing string: " << string << std::endl;

    std::cout << std::endl;
}

int main(void)
{
    test_zlib();
    test_eigen();
    test_glm();
    test_vulkan();
    return EXIT_SUCCESS;
}
