/**
 * @copyright DEFAULT
 * @brief: Vulkan RenderPass
 * @note : N/A
 */
#pragma once

#ifndef RenderPass_H
#define RenderPass_H

namespace VulkanEngine
{

    class VKENGINE_API RenderPass
    {
    public:
        RenderPass();

        virtual ~RenderPass(void);

        VkRenderPassKHR create();

        void create(VkInstance instance, GLFWwindow* window);

        /* Perform render pass */
        void render(VkCommandBuffer cmd);

        /* Begin render pass */
        void begin(VkRenderPassBeginInfo info);

        /* End render pass */
        void end();

        /* Return render pass reference */
        void pass();

    private:
        /* Render pass object */
        VkRenderPass m_renderPass;

    };
}
#endif