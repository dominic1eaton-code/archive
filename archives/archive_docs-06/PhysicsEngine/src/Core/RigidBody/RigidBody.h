

class Transform;

namespace PhysicsEngine
{

class RigidBody
{
public:
    RigidBody();
    virtual ~RigidBody(void);


private:
    Transform* m_transform;

};

}