/**
 * @header
 * @copyright
 * @brief Reactor pattern test
 * @note 
 */

// #include <unistd.h> // for linux pipes
#include <thread>
#include <vector>
#include <map>
#include <winsock2.h>
#include <atomic>
#include <array>
#include <iostream>
#include <stdexcept>

/*
 * Events are of types READ, WRITE, and EXCEPT(tion) 
 */
enum class EventType
{
    READ,
    WRITE,
    EXCEPT
};

class Event
{
    Event() = default;

    virtual ~Event(void) = default;

private:

    EventType type;

};

class EventHandler
{
    EventHandler() = default;

    virtual ~EventHandler(void) = default;

    virtual void handleEvent(Event e);

    // virtual void 
};

class Reactor
{
public:
    Reactor() : m_dispatching(false)
    {
        // uint32_t ret = pipe(m_wakeupPipe.data());
        
    };

    virtual ~Reactor(void) = default;

    void registerEventHandler(EventHandler* eventHandler);
    
    void unregisterEventHandler(EventHandler* eventHandler);

    void handleEvents(const struct timeval* timeout = nullptr);

    void unblock();

private:

    void dispatch();

    void setup();

    void sendWakeup();

    void handleWakeup();

    std::map<uint32_t, EventHandler*> m_eventHandlers;

    std::vector<fd_set> fds;
    
    std::atomic_bool m_dispatching;

    std::array<uint32_t, 2> m_wakeupPipe;

};

void Reactor::registerEventHandler(EventHandler* eventHandler)
{

}

void Reactor::unregisterEventHandler(EventHandler* eventHandler)
{

}

// void Reactor::handleEvents(const struct timeval* timeout = nullptr)
// {

// }

void Reactor::unblock()
{

}

void Reactor::dispatch()
{

}

void Reactor::setup()
{

}


int main()
{
    Reactor reactor;

    // std::thread reactorThread();

    // reactorThread.join();

    return 0;
}


