/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once
#ifndef VFence_h
#define VFence_h

#include "Ogun/Core/VObject.h"
#include <vector>
#include <string>

namespace ogun
{

class VFenceSet : public VObject<VFenceSet>
{
public:
    VFenceSet();

    VFenceSet(std::string name, uint32_t count, VkFenceCreateFlagBits flags, VkDevice device);

    virtual ~VFenceSet(void) = default;

    std::string name() const { return m_name; }

    std::vector<VkFence> set() const { return m_fenceSet; }

private:

    std::string m_name;

    uint32_t m_count; 

    std::vector<VkFence> m_fenceSet;

};

class VFences : public VObject<VFences>
{
public:
    VFences() = default;

    virtual ~VFences(void) = default;

    VFenceSet* find(std::string name);

    void create(std::string name, uint32_t count, VkFenceCreateFlagBits flags, VkDevice device);

    void data();

private:

    std::vector<VFenceSet*> m_fences;

};

} // namespace ogun

#endif // VFence_h