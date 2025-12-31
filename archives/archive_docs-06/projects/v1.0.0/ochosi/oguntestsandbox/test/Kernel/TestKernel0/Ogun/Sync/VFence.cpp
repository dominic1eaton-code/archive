/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VFence.h"
#include <string>
#include <set>

using namespace ogun;

VFenceSet::VFenceSet(std::string name, uint32_t count, VkFenceCreateFlagBits flags, VkDevice device)
    : m_name(name)
    , m_count(count)
{
    m_fenceSet.resize(count);
    VkFenceCreateInfo fenceInfo{};
    fenceInfo.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
    fenceInfo.flags = flags;

    for (uint32_t i = 0; i < count; i++)
    {
        createvk(vkCreateFence(device, &fenceInfo, nullptr, &m_fenceSet[i]));
    }
}

void VFences::create(std::string name, uint32_t count, VkFenceCreateFlagBits flags, VkDevice device)
{
    VFenceSet* fenceSet = new VFenceSet(name, count, flags, device);
    m_fences.push_back(fenceSet);
}

VFenceSet* VFences::find(std::string name)
{
    for (auto fence : m_fences)
    {
        if (fence->name() == name)
        {
            return fence;
        }
    }
    return nullptr;
}
