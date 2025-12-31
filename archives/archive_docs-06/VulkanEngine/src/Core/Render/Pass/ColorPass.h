/**
 * @copyright DEFAULT
 * @brief: Vulkan ColorPass. Binds graphics pipelines and render commands
 * @note : N/A
 */
#pragma once

#ifndef ColorPass_H
#define ColorPass_H

namespace VulkanEngine
{

    class VKENGINE_API ColorPass
    {
    public:
        ColorPass();

        virtual ~ColorPass(void);

        VkColorPassKHR create();

        void create(VkInstance instance, GLFWwindow* window);

        /* Perform render pass */
        void render(VkCommandBuffer cmd);

        /* Begin render pass */
        void begin(VkColorPassBeginInfo info);

        /* End render pass */
        void end();

        /* Return render pass reference */
        void pass();

    private:
        /* Render pass object */
        VkColorPass m_ColorPass;

    };
}
#endif