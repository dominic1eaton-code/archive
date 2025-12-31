/**
 * @copyright DEFAULT
 * @brief: Renderer main class. Converts a logical scene (e.g. from an PhysicsEngine) to a render scene,
 *         via a series of rendering passes and draws result to screen.
 * @note : N/A
 */
#pragma once
#ifndef PhysicsEngine_H
#define PhysicsEngine_H

#include <vulkan/vulkan.h>

namespace PhysicsEngine
{

class PhysicsEngine : public SComponent<PhysicsEngine>
{
public:
    PhysicsEngine() = default;
    virtual ~PhysicsEngine(void) = default;

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

} // RenderPhysicsEngine

#endif // PhysicsEngine_H