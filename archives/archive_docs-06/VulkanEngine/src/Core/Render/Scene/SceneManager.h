
namespace VulkanEngine
{
    class Scene;

    class SceneManager
    {
    public:
        SceneManager();
        virtual ~SceneManager(void);

        /* load a scene */
        bool load();

        /* save current scene */
        bool save();

    private:
        /* Currently loaded scene */
        Scene* m_currentScene;

    };
} // VulkanEngine
