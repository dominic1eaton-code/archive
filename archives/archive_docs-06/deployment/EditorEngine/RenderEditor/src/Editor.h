/**
 * @copyright DEFAULT
 * @brief: Renderer main class. Converts a logical scene (e.g. from an editor) to a render scene,
 *         via a series of rendering passes and draws result to screen.
 * @note : N/A
 */
#pragma once
#ifndef EDITOR_H
#define EDITOR_H

#include <vulkan/vulkan.h>

namespace RenderEditor
{

class Editor : public SComponent<Editor>
{
public:
    Editor() = default;
    virtual ~Editor(void) = default;

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

} // RenderEditor

#endif // EDITOR_H