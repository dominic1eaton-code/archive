/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef SHADER_H
#define SHADER_H

#include <string>
#include "VulkanDefines.h"
#include <vulkan/vulkan.h>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class RENGINE_API Shader
    {
    public:
        Shader();
        Shader(VkDevice device, std::string shader, VkShaderStageFlagBits stage);
        virtual ~Shader(void);

        /* */
        bool create();

        /* */
        VkShaderModule shader();

        /* */
        const char* entryPoint();

        /* */
        VkShaderStageFlagBits stage();

    private:
        /* */
        VkShaderModule m_shaderModule;

        /* */
        VkShaderModuleCreateInfo m_createInfo;

         /* creation type */
         VkStructureType m_sType;

         /* Pointer to extension structure */
         const void* m_pNext;

         /* instance creation flags */
         VkInstanceCreateFlags m_flags;

        /* */
        VkShaderStageFlagBits m_stage;

        /* */
        std::string m_entryPoint;

        /* */
        VkDevice m_device;

        /* */
        std::string  m_shaderName;

        /* */
        bool m_created;

        /* */
        std::string m_defaultEntryPoint;

}

#endif // SHADER_H