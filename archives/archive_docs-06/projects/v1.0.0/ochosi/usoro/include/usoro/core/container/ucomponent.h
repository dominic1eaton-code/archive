/**
 * @copyright
 * @brief
 * @note
 */

#pragma once
#ifndef ucomponent_h
#define ucomponent_h
#include <string>
#include <cstdint>

namespace usoro
{
    
class UBaseComponent
{
public:
    UBaseComponent(std::string name, uint32_t id, uint32_t divisor) 
        : m_name(name)
        , m_id(id)
        , m_divisor(divisor)
        , m_active(false)
    {}

    virtual ~UBaseComponent(void) = default;
    
    std::string name() const { return m_name; }

    uint32_t id() const { return m_id; }

    uint32_t divisor() const { return m_divisor; }

    bool active() const { return m_active; }

    void activate() { m_active = true; }

    void deactivate() { m_active = false; }

private:

    std::string m_name;

    uint32_t m_id;

    uint8_t m_divisor;

    bool m_active;
};


class UComponent : public UBaseComponent
{
public:
    UComponent()
        : UBaseComponent("", 0, 1)
    {}
    virtual ~UComponent(void) = default;

    /* FSM state methods */

    virtual void initialize() = 0;

    virtual void configure() = 0;

    virtual void update() = 0;

    virtual void pause() = 0;

    virtual void reset() = 0;

    virtual void shutdown() = 0;
};

};

#endif // ucomponent_h