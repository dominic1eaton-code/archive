/**
 * @copyright DEFAULT
 * @brief
 * @note
 */
#include "VSemaphore.h"
#include <string>
#include <set>

using namespace ogun;

VSemaphoreSet::VSemaphoreSet(std::string name, uint32_t count, VkDevice device)
    : m_name(name)
    , m_count(count)
{
    m_semaphoreSet.resize(count);
    VkSemaphoreCreateInfo semaphoreInfo{};
    semaphoreInfo.sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO;

    for (uint32_t i = 0; i < count; i++)
    {
        createvk(vkCreateSemaphore(device, &semaphoreInfo, nullptr, &m_semaphoreSet[i]));
    }
}

VSemaphores::VSemaphores()
    : m_semaphores({})
{}

void VSemaphores::create(std::string name, uint32_t count, VkDevice device)
{
    VSemaphoreSet* semaphoreSet = new VSemaphoreSet(name, count, device);
    m_semaphores.push_back(semaphoreSet);
}

VSemaphoreSet* VSemaphores::find(std::string name)
{
    for (auto semaphore : m_semaphores)
    {
        if (semaphore->name() == name)
        {
            return semaphore;
        }
    }
    return nullptr;
}
