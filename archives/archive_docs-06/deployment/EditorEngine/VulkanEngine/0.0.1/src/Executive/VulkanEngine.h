/**
 * @copyright DEFAULT
 * @brief: Renderer main class. Converts a logical scene (e.g. from an editor) to a render scene,
 *         via a series of rendering passes and draws result to screen.
 * @note : N/A
 */
#pragma once
#ifndef VULKANENGINE_H
#define VULKANENGINE_H

#include <vulkan/vulkan.h>

namespace VulkanEngine
{

class Engine : public SComponent<Engine>
{
public:
    Engine() = default;
    virtual ~Engine(void) = default;

    /* */
    void configure();

    /* */
    void initialize();
    
    /* */
    void update();
    
    /* */
    void pause();

    /* */
    void shutdown();

private:

};

} // VulkanEngine

#endif // VULKANENGINE_H