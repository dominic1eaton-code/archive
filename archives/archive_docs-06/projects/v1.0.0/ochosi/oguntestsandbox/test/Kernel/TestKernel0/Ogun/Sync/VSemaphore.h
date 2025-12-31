/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VSemaphore_h
#define VSemaphore_h

#include "Ogun/Core/VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VSemaphoreSet : public VObject<VSemaphoreSet>
{
public:
    VSemaphoreSet();

    VSemaphoreSet(std::string name, uint32_t count, VkDevice device);

    virtual ~VSemaphoreSet(void) = default;

    std::string name() const { return m_name; }

    std::vector<VkFence> set() const { return m_semaphoreSet; }

private:

    std::string m_name;

    uint32_t m_count; 

    std::vector<VkSemaphore> m_semaphoreSet;

};

class VSemaphores : public VObject<VSemaphores>
{
public:
    VSemaphores();

    virtual ~VSemaphores(void) = default;

    VSemaphoreSet* find(std::string name);

    void create(std::string name, uint32_t count, VkDevice device);

    void data();

private:

    std::vector<VSemaphoreSet*> m_semaphores;

};

} // namespace ogun

#endif // VSemaphore_h