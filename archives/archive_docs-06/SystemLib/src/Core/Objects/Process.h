


namespace SystemLib
{

class Process
{
public:
    Process();
    virtual ~Process(void);

    void begin();

    void end();

private:
    bool m_isRunning;
};

}; // SystemLib