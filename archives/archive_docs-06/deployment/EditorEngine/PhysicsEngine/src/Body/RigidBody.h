/**
 * @brief 
 * @units
 *  kg  kilogram
 *  m   meter
 *  s   second
 *  f   feet
 *  t   time
 */


struct Vector3 ;

namespace PhysicsEngine
{

class RigidBody
{
public: 
    RigidBody() = default;
    virtual ~RigidBody(void) = default;

    /* current position of RigidBody [m] */
    Vector3 m_position;

    /* velocity of RigidBody [m / s] */
    Vector3 m_velocity;

    /*  acceleration of RigidBody [m / s^2]  */
    Vector3 m_acceleration;

    /* */
    Transform m_transform;

    /* */
    Quaternion m_rotation;

    /* */
    Quaternion m_orientation;

    /* velocity damping factor */
    float damping;

    /* mass of RigidBody [kg] */
    float m_mass;

    /* total lifetime of RigidBody [t] */
    float lifetime;
};

}