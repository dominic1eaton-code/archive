/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef SCENEMANAGER_H
#define SCENEMANAGER_H

#include <vector>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class Scene;

    class RENGINE_API SceneManager
    {
    public:
        SceneManager();
        // SceneManager();
        virtual ~SceneManager(void);

        /* */
        void change();

        /* */
        void load();

    private:
        std::vector<Scene> m_scenes;
    };
}

#endif // SCENEMANAGER_H