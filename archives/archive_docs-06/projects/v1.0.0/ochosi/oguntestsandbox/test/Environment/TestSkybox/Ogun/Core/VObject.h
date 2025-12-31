/**
 * @header
 * @copyright
 * @brief Base class for vulkan objects
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

    /**
     * return created state of vulkan object
     * @return is vulkan object created?
     */
    bool create() const { return m_created; }

    /**
     * return vulkan object ID
     * @return object ID
     */
    uint32_t id() const { return m_id; }

    /**
     * validate creation vulkan object
     * @param i_vObj result of created vulkan object
     */
    void createvk(VkResult i_vObj)
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

private:

    void generateID()
    {
        m_id = 0;
    }

    bool m_created = false;
    
    uint32_t m_id = 0;

};

} // namespace ogun

#endif // VObject_h