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

struct GameState
{

};

struct RenderPacket
{

};

void play();
void stop();
void pause();
void reset();


}

#endif // oru_game_h