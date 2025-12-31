/**
 * @brief 
 * 
 */

#include <vector>

namespace GroundVehSim
{

class SComponent;
class Piston;
class Valve;
class CylinderHead;

class Piston
{
public:
    Piston();
    virtual ~Piston(void) = default;

private:
    /* */
    CylinderHead* m_cylinderHead;

    /* */
    Valve* m_intakeValve;

    /* */
    Valve* m_exhaustValve;

};

}