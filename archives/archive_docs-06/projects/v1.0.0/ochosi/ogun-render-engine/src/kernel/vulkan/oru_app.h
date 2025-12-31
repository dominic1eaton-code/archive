/**
 * @copyright
 * @brief
 * @note
 */

#ifndef oru_game_h
#define oru_game_h
#include <cstdint>

namespace oru
{

struct AppState
{
    uint32_t shader_system_mem_requirement;
    void* shader_system_state;
};


void initialize();
void configure();
void start();
void stop();
void pause();
void reset();
void shutdown()


}; // namespace oru

#endif // oru_app_h