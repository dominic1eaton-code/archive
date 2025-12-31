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
class Terrain;

enum RenderObjectPrimitives
{
    MESH,
    LIGHT,
    TERRAIN,
    ENVIRONMENT,
    CAMERA
}

/* main test application */
void call();

void initialize()
{
    /* Init editor scene */
    initDefaultEditorScene();

    /* Init Renderer */
    initRenderer();
}

void update()
{
    /* Render editor scene */
    updateRenderer();
}
void initDefaultEditorScene()
{
    // triangle
    Mesh* triangleMesh;
    Material* triangleMaterial;
    Transform triangleTransform = Transform(Position(0, 0, 0),
                                            Rotation(0, 0, 0),
                                            Scale(0, 0 ,0));
    Model* triangle = new Model("triangle0",
                                triangleMesh,
                                triangleMaterial,
                                triangleTransform);

    // cameras
    Camera* camera = new Camera();

    // environment
    Environment* environment = new Environment();

    // lights
    PointLight* pointlight = new PointLight();
    
    // terrain
    Terrain* terrain = new Terrain();

    // create scene
    EditorScene* editorScene = new EditorScene();
    editorScene->add(triangle);
    editorScene->add(camera);
    editorScene->add(environment);
    editorScene->add(pointlight);
    editorScene->add(terrain);
}

void initRenderer()
{
    VkApplicationInfo appInfo{};
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "RenderEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "RenderEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    Renderer* m_renderer = new Renderer();
    m_renderer->initialize(appInfo);
}

void initAssets()
{
    // load shaders

    // load textures

    // load models
}

void updateRenderer()
{
    while (m_renderer->isRunning())
    { 
        SDL_Event event;
        while (SDL_PollEvent(&event))
        {
            // poll until all events are handled!
            // decide what to do with this event.
            if (event.type == SDL_QUIT)
            {
                SDL_Log("Program quit after %i ticks", event.quit.timestamp);
                m_renderer->shutdown();
            }
        }

        // update game state, draw the current frame
        m_renderer->update(editorScene);
    }
}

int main(int argc, char **argv) 
{
    TriangleApplication* app;

    try
    {
        app->call();
    } 
    catch (const std::exception& e)
    {
        std::cerr << e.what() << std::endl;
        return EXIT_FAILURE;
    }
    return EXIT_SUCCESS;
}
