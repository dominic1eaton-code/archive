/**
 * @copyright DEFAULT
 * @brief: 
 * @note : N/A
 */
// #include <SDL2/SDL.h>
#include <iostream>
#include <filesystem>
#include <vector>
#include "Logger.h"
#include "Renderer.h"

namespace fs = std::filesystem;

int main(int argc, char **argv) 
{
    RenderEngine::Renderer* m_renderer = new RenderEngine::Renderer();
    m_renderer->initialize();
    m_renderer->configure();
    m_renderer->update();

    // cleanup
    return 0;
}
