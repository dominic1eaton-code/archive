/**
 * @copyright DEFAULT
 * @brief: Vulkan main running Instance interface
 * @note : N/A
 */
#pragma once
#ifndef VINSTANCE_H
#define VINSTANCE_H

namespace VulkanEngine
{
class VulkanDebugger;

class VInstance
{
public:
    VInstance();
    
    VInstance(VkApplicationInfo appInfo);

    virtual ~VInstance(void);

private: 
    VulkanDebugger* m_debugger;

};

} // VulkanEngine

#endif // VINSTANCE_H
