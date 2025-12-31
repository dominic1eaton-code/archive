/**
 * @copyright
 * @brief
 * @note
 */

#pragma once
#ifndef vulkan_engine_h
#define vulkan_engine_h

#include "vulkan_model.h"
#include <vulkan/vulkan_win32.h>
#include <Windows.h>

namespace vulkan
{

struct CameraParameters
{
    float zoom;
};

// uint32_t current_active_object;

void init_Vulkan(HWND hwnd, VkExtent2D window_extent, VFrame* frame);
void draw_frame(float tick, VFrame* frame);
void resize_frame_buffer(uint32_t width, uint32_t height, VFrame* frame);
void move_cursor(double xpos, double  ypos, glm::vec2& cursor);

void package_game();
void deploy_game();
void run_game();
void pause_game();
void reset_game();
void stop_game();
void save_game();
void load_game();
void hot_reload_shaders();
void select_object();
void deselect_object();

void translate_camera(float angle, glm::vec3 axis, uint32_t type, ogun::VCamera& camera);
void zoom_camera(ogun::VCamera& camera, float rotation);
void rotate_camera(ogun::VCamera& camera, float rotation, glm::vec3 axis);
void change_camera_perspective(ogun::VCamera& camera);
void translate_mesh();
void rotate_mesh();
void scale_mesh();
void translate_object(uint32_t object_index, glm::vec3 translation, bool bflip);

void create_camera(uint32_t id, CameraParameters parameters);
void create_terrain(uint32_t id);
void create_skybox(uint32_t id);
void create_mesh(uint32_t id);
void create_light(uint32_t id);
void create_environment(uint32_t id);
void create_primitive(uint32_t id);
void create_animation(uint32_t id);
void create_material(uint32_t id);
void create_shader(uint32_t id);
void create_skeleton(uint32_t id);
void create_scene(uint32_t id);
void create_font(uint32_t id);
void create_model(uint32_t id);
void create_sound(uint32_t id);
void create_heightmap(uint32_t id);
void create_texture(uint32_t id);
void create_image(uint32_t id);
void create_ui();

void destroy_camera(uint32_t id);
void destroy_terrain(uint32_t id);
void destroy_skybox(uint32_t id);
void destroy_mesh(uint32_t id);
void destroy_light(uint32_t id);
void destroy_environment(uint32_t id);
void destroy_primitive(uint32_t id);
void destroy_animation(uint32_t id);
void destroy_material(uint32_t id);
void destroy_shader(uint32_t id);
void destroy_skeleton(uint32_t id);
void destroy_scene(uint32_t id);
void destroy_font(uint32_t id);
void destroy_model(uint32_t id);
void destroy_sound(uint32_t id);
void destroy_heightmap(uint32_t id);
void destroy_texture(uint32_t id);
void destroy_image(uint32_t id);

void update_camera(uint32_t id, CameraParameters parameters);
void update_terrain(uint32_t id);
void update_skybox(uint32_t id);
void update_mesh(uint32_t id);
void update_light(uint32_t id);
void update_environment(uint32_t id);
void update_primitive(uint32_t id);
void update_animation(uint32_t id);
void update_material(uint32_t id);
void update_shader(uint32_t id);
void update_skeleton(uint32_t id);
void update_scene(uint32_t id);
void update_font(uint32_t id);
void update_model(uint32_t id);
void update_sound(uint32_t id);
void update_heightmap(uint32_t id);
void update_texture(uint32_t id);
void update_image(uint32_t id);

void retrieve_camera(uint32_t id);
void retrieve_terrain(uint32_t id);
void retrieve_skybox(uint32_t id);
void retrieve_mesh(uint32_t id);
void retrieve_light(uint32_t id);
void retrieve_environment(uint32_t id);
void retrieve_primitive(uint32_t id);
void retrieve_animation(uint32_t id);
void retrieve_material(uint32_t id);
void retrieve_shader(uint32_t id);
void retrieve_skeleton(uint32_t id);
void retrieve_scene(uint32_t id);
void retrieve_font(uint32_t id);
void retrieve_model(uint32_t id);
void retrieve_sound(uint32_t id);
void retrieve_heightmap(uint32_t id);
void retrieve_texture(uint32_t id);
void retrieve_image(uint32_t id);

}; //  namespace vulkan

#endif // vulkan_engine_h