/**
 * @copyright DEFAULT
 * @brief: Generic Window wrapper class
 * @note : N/A
 */
#pragma once

#include <string>

#ifndef VISTANCE_H
#define VISTANCE_H

namespace VulkanEngine
{
    class VKENGINE_API VInstance
    {
    public:
        VInstance();
        virtual ~VInstance(void);

        /* Create vulkan object */
        bool create();

    private:
        /* Window object */
        SDL_Window* m_instance;
        
        /* Check default supported features on machine for vulkan instance */
        template<typename T>
        bool checkDefaultSupport(T defaultSupportVector, T availableSupportVector, T &support);
    };
} // VulkanEngine

#endif // VISTANCE_H
