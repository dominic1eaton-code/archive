/**
 * @copyright DEFAULT
 * @brief: Renderer main class. Converts a logical scene (e.g. from an editor) to a render scene,
 *         via a series of rendering passes and draws result to screen.
 * @note : N/A
 */
#pragma once
#ifndef RENDERER_H
#define RENDERER_H

#include <string>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
class SceneManager;
class ShaderManager;
class SComponent;

class RENGINE_API Renderer : public SComponent
{
public:
    Renderer();
    virtual ~Renderer(void);

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

    /* */
    void reset();

private:
    /* */
    void processEngineUpdates();

    /* */
    void processEditorUpdates();

    /* */
    void processSceneUpdates();

    /* Internal reference to a logical scene to be rendered. Holds information about the scene 
       and tells renderer to generate scene objects based on parameters from recieved sceneMessage.
       updated by sceneMessage */
    SceneManager* m_sceneManager;

    /* Reference to shader library. Updated by shaderLibraryMessage */
    ShaderManager* m_shaderManager;

    /* Current render frame in flight */
    int m_currentFrame;


};


} // RenderEngine
