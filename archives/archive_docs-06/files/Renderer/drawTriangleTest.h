/**
 * @copyright DEFAULT
 * @brief: Draw Triangle render test
 * @note : N/A
 */

#include <iostream>

class Renderer;
class Model;
class Material;
class Transform;
class Mesh;
class Camera;
class Environment;
class PointLight;
class EditorScene;

/* main test application */
class TriangleApplication
{
public:
    void call();
    void initialize();
    void update();

private:
    void initDefaultEditorScene();
    void initRenderer();
    void updateRenderer();

    EditorScene* m_editorScene;
    Renderer* m_renderer;
};
