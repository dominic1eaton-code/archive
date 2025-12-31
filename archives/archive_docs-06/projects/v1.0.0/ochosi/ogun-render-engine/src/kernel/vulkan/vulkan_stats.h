/**
 * @copyright
 * @brief
 * @note
 */
#pragma once
#ifndef vulkan_stats_h
#define vulkan_stats_h
#include <cstdint>

namespace vulkan
{

struct EngineStats
{
    float fps;
    uint32_t frame_count;
};

};

#endif // vulkan_stats_h