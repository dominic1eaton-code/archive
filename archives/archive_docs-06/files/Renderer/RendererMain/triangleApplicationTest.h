/**
 * @copyright DEFAULT
 * @brief: Draw Triangle render test
 * @note : N/A
 */
#pragma once
#ifndef TRIANGLEAPPLICATION_TEST_H
#define TRIANGLEAPPLICATION_TEST_H

namespace RenderEngine
{
    class Renderer; 
    class Engine;
    class EditorScene;
}

namespace RenderEngineTest
{
    /* main test application */
    class TriangleApplication
    {
    public:
        TriangleApplication();
        virtual ~TriangleApplication(void);
        void call();
        void initialize();
        void update();

    private:
        void initEngine();
        void initRenderer();
        void initSceneManually();
        void initSceneFromFile();
        void updateRenderer();

        RenderEngine::EditorScene* m_editorScene;
        RenderEngine::Renderer* m_renderer;
    };
} // RenderEngineTest

#endif // TRIANGLEAPPLICATION_TEST_H