


namespace SystemLib
{

class Component
{
public:
    Component();
    virtual ~Component(void);

    void begin();

    void end();

private:
    bool m_isRunning;
};

}; // SystemLib