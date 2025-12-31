/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
#include "VulkanCommon.h"
#include <fstream>

using namespace RenderEngine;

/*
 *  @brief: check vulkan object has been created successfully
 */
bool Utilities::checkVKCreation(VkResult i_vObj)
{
    if (i_vObj != VK_SUCCESS) 
    {
        throw std::runtime_error("failed to create vulkan object !");
        return false;
    }
    else
    {
        // std::cout << "created vulkan object " << std::endl; 
        return true;
    }
}

bool Utilities::validateVulkanObject(VkResult i_vObj)
{
    if (i_vObj != VK_SUCCESS) 
    {
        throw std::runtime_error("failed to create vulkan object !");
        return false;
    }
    else
    {
        // std::cout << "created vulkan object " << std::endl; 
        return true;
    }
}

/*
 * @brief: read data from configuration file
 */
void Utilities::readConfigurationData()
{
    // @todo read configuration files and populate data structures
}

/*
 * @brief: perform string comparison to determine support data
 */
std::vector<const char*> Utilities::checkDefaultSupport(std::vector<std::string>& defaultSupportVector,
                                                        std::vector<std::string>& availableSupportVector)
{
    // https://stackoverflow.com/questions/47683551/push-back-keeps-rewriting-all-entries-in-the-vector-to-the-item-pushed-back
    std::vector<const char*> support;

    // Check for support of default values in input array
    for (auto& defaultSupport : defaultSupportVector)
    {
        bool supportFound = false;
        for (auto& availableSupport : availableSupportVector)
        {
            if (strcmp(defaultSupport.c_str(), availableSupport.c_str()) == 0)
            {
                supportFound = true;
                support.push_back(defaultSupport.c_str());
                break;
            }
        }
    }
    return support;
}

/*
 * @brief: read all of the bytes from the specified file and return them in a byte 
 *         array managed by std::vector. We start by opening the file with two flags:
 *             ate   : Start reading at the end of the file
 *             binary: Read the file as binary file (avoid text transformations)
 */
std::vector<char> Utilities::readFile(const std::string& filename)
{
    std::ifstream file(filename, std::ios::ate | std::ios::binary);
    if (!file.is_open())
    {
        throw std::runtime_error("failed to open file!");
    }

    // The advantage of starting to read at the end of the file is that we
    // can use the read position to determine the size of the file and allocate
    // a buffer
    size_t fileSize = (size_t) file.tellg();
    std::vector<char> buffer(fileSize);

    // seek back to the beginning of the file and read all of the bytes at once
    file.seekg(0);
    file.read(buffer.data(), fileSize);

    // close the file and return the bytes
    file.close();
    return buffer;
}
