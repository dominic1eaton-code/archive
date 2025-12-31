

#include "Particle.h"

using namespace PhysicsEngine;


Vector3 Particle::force()
{
    return m_mass * m_acceleration;
}

Vector3 Particle::position()
{
    m_position += m_position * m_velocity * time * m_acceleration * time * time * 0.5f; 
}

Vector3 Particle::velocity()
{
    m_velocity += m_velocity * damping + m_acceleration * time; 
}

Vector3 Particle::drag()
{
    m_velocity += m_velocity * damping + m_acceleration * time; 
}






