/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef SCENE_H
#define SCENE_H

#include <iostream>
#include <string>
#include <filesystem>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class SceneObject;
    class Camera;
    class Light;
    class Mesh;
    class Terrain;
    class Environment;

    class RENGINE_API Scene
    {
    public:
        Scene();
        // Scene();
        virtual ~Scene(void);

    private:
        /* */
        void loadSceneFile(fs::path sceneFile);

        /* */
        void load();

        /* */
        template<class ReturnType>
        ReturnType* createSceneObject(std::string name);


    };
}

#endif // SCENE_H