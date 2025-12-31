

template<class C>
class Component
{
public:
    Component();
    virtual ~Component(void);
    
    virtual void initialize();

    void configure();

    void update();

    void pause();

    void reset();

    void shutdown();

    bool active() const { return m_active; }

    void activate() { m_active = true; }

    void deactivate() { m_active = false; }

protected:

    bool m_active = false;

    /*
     * runtime frequency division
     * 1 ~= 60 hz
     * 30hz
     * 45hz
     * 120hz
     * ...
     */
    int divisor = 1;

};