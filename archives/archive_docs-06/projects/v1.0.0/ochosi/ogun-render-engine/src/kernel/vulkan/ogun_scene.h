/**
 * @copyright
 * @brief
 * @note
 */

#pragma once
#ifndef ogun_scene_h
#define ogun_scene_h
#include <cstdint>
#include <glm/glm.hpp>
#include <vector>
#include "vulkan_shader.h"

namespace ogun
{

struct OMeshBuffer
{
    std::vector<sema::Vertex> vertices;
    std::vector<uint32_t> indices;
    std::vector<glm::mat4> models;
    std::vector<uint32_t> offsets;
    std::vector<uint32_t> vsizes;
    std::vector<uint32_t> isizes;
    uint32_t offset;
    bool empty = true;
    bool indexed;
    uint32_t materialID;
};

struct OLightBuffer
{

};

struct OCameraBuffer
{

};



struct OEnvironmentBuffer
{

};

struct OTerrainBuffer
{

};

struct OMesh
{

};

struct OMaterial
{

};

struct OCamera
{

};

struct OLight
{

};

// https://tangrams.github.io/heightmapper/
struct OTerrain
{

};

struct OEnvironment
{

};

struct GPUEnvironemnt
{

};

struct GPUTerrain
{

};

struct GPUMaterial
{

};

struct GPUParticlesParameters
{
    float deltaTime;
};

struct GPUParticle
{
    glm::vec2 position;
    glm::vec2 velocity;
    glm::vec4 color;
};

struct GPUCamera
{
    alignas(16) glm::mat4 model;
    alignas(16) glm::mat4 view;
    alignas(16) glm::mat4 proj;
};

struct GPULight
{
    glm::vec4 direction; // w = inner cutoff
    glm::vec4 position; // w = outer cutoff
    glm::vec4 ambient;
    glm::vec4 diffuse;
    glm::vec4 specular;
    glm::vec4 parameters;
    glm::vec4 options;
};

struct GPUMesh
{
    glm::mat4 model;
};

struct GPUMeshInfo
{
    uint32_t meshID;
};

struct GPUScene
{
    glm::vec4 view;
    glm::vec4 parameters; // x = number_scene_lights
};

struct VCamera
{
    glm::vec3 position;
    glm::vec3 front;
    glm::vec3 up;
    float zoom;
    float speed;
    float speed_multiplier;
    float znear;
    float zfar;
    float zoom_angle; // [degrees]
    float aspect;
    glm::mat4 model;
    uint32_t projection_mode; // 0 = perspective; 1 = orthographic
};

const uint32_t WIDTH = 800;
const uint32_t HEIGHT = 600;
const uint32_t PARTICLE_COUNT = 10; // = 8192;
const float PI = 3.14159265358979323846f;
// std::vector<GPUCamera> cameras;

void create_test_compute_data(std::vector<uint32_t>& compute_data);
void create_test_scene(std::vector<OMeshBuffer>& meshes, std::vector<GPULight>& lights, std::vector<VCamera>& cameras, std::vector<GPUParticle>& particles);
void load_scene(uint32_t sceneID);
void save_scene();
void create_scene();
void update_scene();
void generate_scene_graph();

void create_mesh();
void create_camera();
void create_terrain();
void create_environment();
void create_light();

// ogun primitives
void create_camera_mesh();
void create_axis_mesh();
// ogun primitives

void append_mesh(OMeshBuffer& buffer, sema::SPrimitive object);
void append_light();
void append_terrain();
void append_camera();
void append_environment();

void remove_mesh(OMeshBuffer& buffer, uint32_t index);

}; // namespace vulkan

#endif // ogun_scene_h