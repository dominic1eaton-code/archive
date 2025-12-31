/**
 * @license
 * @brief core vulkan objects
 */
#ifndef vulkan_scene_h
#define vulkan_scene_h
#include "vulkan_core.h"

namespace ogun
{

    struct Mesh
    {
    };

    struct RObject
    {
    };

    enum LightTypes
    {
        DIRECTIONAL,
        POINT,
        SPOT
    };

    void load_scene(uint32_t sceneID);
    void create_scene();

    void transform_object();
    void rotate_object();
    void translate_object();
    void scale_object();

    void zoom_camera();
    void translate_camera();
    void rotate_camera();

    void create_camera();
    void create_mesh();
    void create_light();
    void create_terrain();
    void create_skybox();
    void create_terrain();

    // shapes
    void create_primitive();
    void create_curve();
    void create_shape();
    void create_point();
    void create_triangle();
    void create_square();
    void create_pentagon();
    void create_hexagon();
    void create_polygon();
    void create_plane();
    void create_circle();
    void create_cube();
    void create_cone();
    void create_cylinder();
    void create_pyramid();
    void create_sphere();
    void create_bezier();
    void create_polyhedron();
    void create_hermite_spline();
}; // namespace ogun

#endif // vulkan_scene_h
