/**
 * @copyright DEFAULT
 * @brief: Scene main class. Converts a logical scene (e.g. from an editor) to a render scene,
 *         via a series of rendering passes and draws result to screen.
 * @note : N/A
 */
#pragma once
#ifndef Scene_H
#define Scene_H

#include <string>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
class Mesh;
class Light;
class Camera;
class Terrain;
class Environment;
class SceneObject;

class RENGINE_API Scene
{
public:
    Scene();
    virtual ~Scene(void);

private:
    SceneObject* objects;

    Mesh m_meshes;

    Light m_lights;

    Camera m_cameras;

    Terrain m_terrains;

    Environment m_environments;
};


} // RenderEngine
