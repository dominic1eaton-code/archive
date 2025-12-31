
#include <vector>

class Mesh;
class Material;
class Transform;

namespace VulkanEngine
{
    class Model
    {
    public:
        Model();
        virtual ~Model(void);

    private:
        /* Logical Model Objects */
        /* Model cameras */
        Mesh* m_mesh;

        /* Model cameras */
        Material* m_material;
    
        /* Model cameras */
        Transform* m_transform;
    };
} // VulkanEngine
