/**
 * @brief 
 * 
 */

#include <vector>

namespace GroundVehSim
{

class SComponent;
class Piston;

class EngineBlock
{
public:
    EngineBlock();
    virtual ~EngineBlock(void) = default;

private:
    std::vector<Piston*> m_pistons;

};

}