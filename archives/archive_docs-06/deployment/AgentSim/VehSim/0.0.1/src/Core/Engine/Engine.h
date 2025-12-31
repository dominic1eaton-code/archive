/**
 * @brief Vehicle engine 
 * 
 */

#include <vector>

namespace GroundVehSim
{

class SComponent;
class EngineBlock;
class Ignition;
class Air;
class Fuel;
class Air;
class Stroke;

class Engine : public SComponent<Engine>
{
public:
    Engine();
    virtual ~Engine(void) = default;
    /* */   
    void configure();

    /* */
    void initialize();
    
    /* */
    void update();
    
    /* */
    void pause();

    /* */
    void shutdown();

private:

    /* Engine operations */
    /* Cycle through engine state machine */
    void cycle();

    /* */
    std::vector<Stroke*> m_strokes;

    /* */
    EngineBlock* m_engineBlock;

    /* */
    Ignition* m_ignition;

    /* */
    Fuel* m_fuel;

    /* */
    Air* m_air;



};

}