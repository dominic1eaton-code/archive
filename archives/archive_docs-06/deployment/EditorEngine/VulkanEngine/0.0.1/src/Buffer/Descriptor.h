/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef DESCRIPTOR_H
#define DESCRIPTOR_H

#include <string>
#include <vector>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class UniformBuffer;

    class RENGINE_API Descriptor
    {
    public:
        Descriptor();
        Descriptor(VkDevice device);
        virtual ~Descriptor(void);

        /* */
        void create();

        /* */
        std::vector<VkDescriptorSet> sets();

        /* */
        VkDescriptorSetLayout layout();

        /* */
        void updateDescriptorSets(std::vector<std::vector<UniformBuffer*>> uniformBuffers);

    private:
        /* */
        uint32_t m_maxPoolSize;

        /* */
        std::vector<UniformBuffer*> m_uniformBuffers;

        /* */
        VkDevice m_device;

        /* */
        VkDeviceSize m_bufferSize;

        /* */
        std::vector<VkDescriptorSet> m_descriptorSets;

        /* */
        VkDescriptorPool m_descriptorPool;

        /* */
        VkDescriptorSetLayout m_descriptorSetLayout;

        /* */
        VkImage m_textureImage;
        
        /* */
        VkDeviceMemory m_textureImageMemory;
        
        /* */
        VkImageView m_textureImageView;
        
        /* */
        VkSampler m_textureSampler;
    };
}

#endif // DESCRIPTOR_H
