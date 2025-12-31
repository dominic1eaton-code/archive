/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VObject_h
#define VObject_h

// #include <vulkan/vulkan_win32.h>
// #include <vulkan/vulkan.h>
#include <string>
#include <iostream>

namespace ogun
{

class VObject
{
public:
    VObject() = default;
    virtual ~VObject(void) = default;

    // static void validate(VkResult i_result, std::string errMsg)
    // {
    //     if (i_result != VK_SUCCESS)
    //     {
    //         // throw error
    //         std::cout << errMsg << " : " << i_result << std::endl;
    //     }
    //     else
    //     {
    //         // on success
    //     }
    // }

protected:

    uint32_t m_id;
};

} // namespace ogun

#endif // VObject_h