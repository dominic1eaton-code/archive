
#include <vector>

class Particle;


class Contact
{
public: 
    Contact();
    virtual ~Contact(void);

    /* */
    std::vector<Particle*> m_particles;

    /* */
    float restitution;

    /* */
    Vector3 normal;
    
    /* penetration of particle into another particle */
    float penetraion; 
    
protected:
    /* apply collision forces to all particles involved in collision */
    float resolve();

};


