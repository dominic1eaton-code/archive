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

class Particle
{
public: 
    Particle() = default;
    virtual ~Particle(void) = default;

    /* current position of particle [m] */
    Vector3 m_position;

    /* velocity of particle [m / s] */
    Vector3 m_velocity;

    /*  acceleration of particle [m / s^2]  */
    Vector3 m_acceleration;

    /* velocity damping factor */
    float damping;

    /* mass of particle [kg] */
    float m_mass;

    /* total lifetime of particle [t] */
    float lifetime;
};

}