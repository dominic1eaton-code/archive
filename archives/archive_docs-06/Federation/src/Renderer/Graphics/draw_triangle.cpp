/**
 * @copyright DEFAULT
 * @brief: TEMP Main Engine execution
 * @note : N/A
 */

Scene* loadScene()
{

    // create scene objects
    // render objects (models)
    Model* triangle = new Model("test");
    Transform triangleTransform = Transform(Position(0, 0, 0),
                                            Rotation(0, 0, 0),
                                            Scale(0, 0 ,0));
    Material* triangleMaterial = new Material("red");
    Mesh* triangleMesh = new Mesh(Primitive(Primitives::triangle));
    triangle.mesh(triangleMesh);
    triangle.material(triangleMaterial);
    triangle.transform(triangleTransform);

    // cameras
    Camera* camera = new Camera();

    // environment
    Environment* environment = new Environment();

    // lights
    PointLight* pointlight = new PointLight();

    // create scene
    Scene* scene = new Scene();
    scene->register(triangle);
    scene->register(camera);
    scene->register(environment);
    scene->register(pointlight);

    return scene;
}

void drawTriangle()
{
    // initialize renderer
    VkApplicationInfo appInfo{};
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "RenderEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "RenderEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    Renderer* renderer = new Renderer();
    renderer->initialize(appInfo);

    // init logical scene
    Scene* scene = loadScene();

    // Main render loop
    while (m_renderer->isRunning())
    { 
        SDL_Event event;
        while (SDL_PollEvent(&event))
        {
            // poll until all events are handled!
            // decide what to do with this event.
            if (event.type == SDL_QUIT)
            {
                SDL_Log("Program quit after %i ticks", e.quit.timestamp);
                m_renderer->shutdown();
            }
        }

        // update game state, draw the current frame
        m_editor->update(scene);
        m_engine->update(scene);
        m_renderer->draw(scene);
    }
}

int main(int argc, char **argv) 
{
    drawTriangle();
    return 0;
}
