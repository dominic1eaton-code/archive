


namespace SystemLib
{

class Mutex
{
public:
    Mutex(); 
    virtual ~Mutex(void);

    /* */
    void lock();

    /* */
    void unlock();
};

};
