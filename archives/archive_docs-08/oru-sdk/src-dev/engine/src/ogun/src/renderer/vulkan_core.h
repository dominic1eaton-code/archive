/**
 * @license
 * @brief core vulkan objects
 */
#ifndef vulkan_core_h
#define vulkan_core_h

#include <vulkan/vulkan.h>
#include <glm/glm.hpp>
#include <assert.h>

namespace ogun
{

    static void validatevk(VkResult i_result)
    {
        assert(i_result == VK_SUCCESS && "vulkan object not created successfully!");
    }

}; // namespace ogun

#endif // vulkan_core_h