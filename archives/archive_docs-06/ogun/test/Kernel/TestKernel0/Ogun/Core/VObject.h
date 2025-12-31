/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VObject_h
#define VObject_h

#include <Vulkan/vulkan.h>
#include <windows.h>

#define GLM_FORCE_RADIANS
#define GLM_FORCE_DEPTH_ZERO_TO_ONE
#define GLM_ENABLE_EXPERIMENTAL
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtx/hash.hpp>


namespace ogun
{

template<class U>
class VObject
{
public:
    VObject() = default;
    virtual ~VObject(void) = default;

    // virtual U& build();

    bool create() const { return m_created; }

    uint32_t id() const { return m_id; }

    void createVk(VkResult i_vObj)
    {
        if (i_vObj != VK_SUCCESS) 
        {
            // throw std::runtime_error("failed to create vulkan object !");
            m_created = false;
        }
        else
        {
            // std::cout << "created vulkan object " << std::endl;
            m_created =  true;
            generateID();
        }
    };

protected:

    void generateID()
    {
        m_id = 0;
    }

private:

    bool m_created = false;
    
    uint32_t m_id = 0;

};

} // namespace ogun

#endif // VObject_h