
#include <vector>

class Camera;
class Environment;
class Light;
class Model;
class Terrain;

namespace VulkanEngine
{
    class File;

    class Scene
    {
    public:
        Scene();
        virtual ~Scene(void);

        /* create the scene */
        bool create();

        /* read .scene file */
        void read(File scenefile);

    private:
        /* Logical Scene Objects */
        /* scene cameras */
        std::vector<Camera*>  m_cameras;
        
        /* scene lights */
        std::vector<Light*> m_lights;

        /* scene models */
        std::vector<Model*> m_models;

        /* scene environment */
        Environment* m_environment;

        /* scene terrain */
        Terrain* m_terrain;
    };
} // VulkanEngine
