/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef COMMAND_H
#define COMMAND_H

#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class ColorPass; // @todo make into template/inherited class
    class Mesh;

    class RENGINE_API Command
    {
    public:
        Command();
        Command(VkDevice device, uint32_t queueFamilyIndex);
        virtual ~Command(void);

        /* @todo make into template */
        void record(std::vector<ColorPass*> passes, std::vector<Mesh*> meshes, uint32_t currentFrame, VkQueue graphicsQueue);

        /* */
        void reset(uint32_t currentFrame);

        /* */
        void submit(VkSemaphore imageAvailableSemaphore,
                    VkSemaphore renderFinishedSemaphore,
                    VkFence inFlightFence,
                    VkQueue m_graphicsQueue,
                    uint32_t currentFrame);

        /* */
        void present(VkSemaphore renderFinishedSemaphore, uint32_t imageIndex, VkQueue presentQueue, VkSwapchainKHR swapchain);

    private:
        /* */
        void create();

        /* */
        void begin(uint32_t currentFrame);

        /* */
        void end(uint32_t currentFrame);

        /* */
        VkDevice m_device;

        /* We have to create a command pool before we can create command buffers.
           Command pools manage the memory that is used to store the buffers and
           command buffers are allocated from them */
        VkCommandPool m_commandPool;

        /* */
        VkCommandPoolCreateInfo  m_commandPoolInfo;

        /* */
        std::vector<VkCommandBuffer> m_commandBuffers;

        /* */
        VkCommandBufferAllocateInfo m_commandBufferAllocInfo;

        /* */
        VkCommandBufferBeginInfo m_beginInfo;

        /* */
        uint32_t m_queueFamilyIndex;

        /* Logging unit */
        LoggingTool::Logger* m_logger;

        /* Logging unit */
        std::string m_logunit;
    };
}

#endif // COMMAND_H