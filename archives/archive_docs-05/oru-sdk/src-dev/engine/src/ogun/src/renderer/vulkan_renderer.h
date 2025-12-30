/**
 * @license
 * @brief core vulkan objects
 */
#ifndef vulkan_renderer_h
#define vulkan_renderer_h
#include "vulkan_model.h"

namespace ogun
{
    enum RendererMode
    {
        INIT,
        CONFIGURE,
        RUN,
        SHUTDOWN,
        PAUSE,
        RESET
    };

    struct AssetLibrary
    {
        std::filesystem::path root;
        std::string shaders = "shaders";
        std::string images = "images";
        std::string scenes = "scenes";
    };

    struct RendererConfiguration
    {
        AssetLibrary asset_library;
        std::string name;
        Version version;
    };

    void init_renderer();
    void configure_renderer();
    void run_renderer();
    void shutdown_renderer();
    void pause_renderer();
    void reset_renderer();

    void save_renderer_state();
    void update_renderer_configuration();
}; // namespace ogun

#endif // vulkan_renderer_h
