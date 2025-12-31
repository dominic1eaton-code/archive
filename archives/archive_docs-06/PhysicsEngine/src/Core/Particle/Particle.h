



namespace PhysicsEngine
{

class Particle
{
public:
    Particle();
    virtual ~Particle(void);

private:
    /* */
    int life;

    /* */
    // position, velocity, acceleration

    /* */
    float mass;

    /* */
    // force, momentum

};

}