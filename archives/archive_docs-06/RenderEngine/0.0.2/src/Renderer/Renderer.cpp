/**
 * @copyright DEFAULT
 * @brief: Renderer wrapper class
 * @note : N/A
 */
#include "Renderer.h"

using namespace RenderEngine;

Renderer::Renderer()
    : m_logunit("Renderer")
{}

Renderer::~Renderer()
{}

void Renderer::configure()
{

}

void Renderer::initialize()
{
    // initial vulkan core 
    // engineInitMessage.engineInfo
    // engineInitMessage.defaultScene; sceneInitMessage
    // engineInitMessage.defaultShaderLibrary; shaderLibraryInitMessage
    m_vulkan->initialize(engineInitMessage, shaderLibraryInitMessage);
    m_sceneManager->initialize(sceneInitMessage);
}

void Renderer::update()
{
    processEditorUpdates();

    processEngineUpdates();

    // draw new scene frame
    // update frames in flight
    m_currentFrame = (m_currentFrame + 1) % Constants::MAX_FRAMES_IN_FLIGHT;
}

void Renderer::pause()
{

}

void Renderer::shutdown()
{

}

void Renderer::reset()
{

}

void Renderer::processEngineUpdates()
{
    // update engine objects
    processSceneUpdates();

    // update render passes

}

void Renderer::processEditorUpdates()
{
    // update user input
    // userInputMessage;

}

void Renderer::processSceneUpdates()
{
    m_scene->update(sceneUpdateMessage);

    // update meshes

    // update lights

    // update cameras

    // update environment
    
    // update terrain

    // populate draw commands and add to command execution buffer
    m_vulkan->record(m_scene);
}
