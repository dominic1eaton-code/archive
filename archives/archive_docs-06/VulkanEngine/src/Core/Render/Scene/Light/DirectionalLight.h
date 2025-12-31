PointLight.h/**
 * @copyright DEFAULT
 * @brief: Vulkan DirectionalLight
 * @note : N/A
 */
#pragma once

#ifndef DirectionalLight_H
#define DirectionalLight_H

namespace VulkanEngine
{
    struct GPULightata 
    {
        glm::vec3 direction; // 
        glm::vec3 ambient;   // 
        glm::vec3 diffuse;   // 
        glm::vec3 specular;  // 
    };

    class VKENGINE_API DirectionalLight
    {
    public:
        DirectionalLight();

        virtual ~DirectionalLight(void);

        VkDirectionalLightKHR create();

        void create(VkInstance instance, GLFWwindow* window);

        /* Perform render pass */
        void render(VkCommandBuffer cmd);

        /* Begin render pass */
        void begin(VkDirectionalLightBeginInfo info);

        /* End render pass */
        void end();

        /* Return render pass reference */
        void pass();

    private:
        /* Render pass object */
        VkDirectionalLight m_DirectionalLight;

    };
}
#endif