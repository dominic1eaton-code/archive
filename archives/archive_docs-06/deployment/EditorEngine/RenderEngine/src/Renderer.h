/**
 * @copyright DEFAULT
 * @brief: Renderer main class. Converts a logical scene (e.g. from an Render) to a render scene,
 *         via a series of rendering passes and draws result to screen.
 * @note : N/A
 */
#pragma once
#ifndef Render_H
#define Render_H

#include <vulkan/vulkan.h>

namespace Render
{

class Render : public SComponent<Render>
{
public:
    Render() = default;
    virtual ~Render(void) = default;

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

} // Render

#endif // Render_H