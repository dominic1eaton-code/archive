/**
 * @copyright
 * @brief
 * @note
 */
#include "ogun_scene.h"
#include "sema_primitives.h"
#include <random>
#include <algorithm>

namespace ogun
{

void append_mesh(OMeshBuffer& buffer, sema::SPrimitive object)
{
    if (!buffer.empty) buffer.offset += object.vertices.size();
    for (auto vert : object.vertices)
    {
        buffer.vertices.push_back(vert);
    }
    for (auto ind : object.indices)
    {
        buffer.indices.push_back(ind + buffer.offset);
    }
    buffer.models.push_back(object.model);
    buffer.offsets.push_back(buffer.offset);
    buffer.vsizes.push_back(object.vertices.size());
    buffer.isizes.push_back(object.indices.size());
    buffer.empty = false;
}

void remove_mesh(OMeshBuffer& buffer, uint32_t index)
{}

void create_test_compute_data(std::vector<uint32_t>& compute_data)
{
    uint32_t n = 0;
    std::generate(compute_data.begin(), compute_data.end(), [&n] { return n++; });
}

void create_test_scene(std::vector<OMeshBuffer>& meshes, std::vector<GPULight>& lights, std::vector<VCamera>& cameras, std::vector<GPUParticle>& particles)
{
    int32_t material0 = -1;
    int32_t material1 = 0;
    int32_t material2 = 1;

    // 2D primitives
    sema::SPrimitive circle0 = sema::generate_circle(1.0f, glm::vec3(4.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f), sema::color::sred, 200, 0.5f, material0);
    sema::SPrimitive bcurve0 = sema::generate_bezier(std::vector<glm::vec3>{glm::vec3(2.0, 0.0, 0.0), glm::vec3(-3.0, 0.0, 0.0), glm::vec3(-4.0, 4.0, 0.0),glm::vec3(0.0, 5.0, 0.0)}, sema::color::sblue, 100, 0.01f, material0);
    sema::SPrimitive hcurve1 = sema::generate_hermite(std::vector<glm::vec3>{glm::vec3(2.0, 0.0, 0.0), glm::vec3(-3.0, 0.0, 0.0)}, std::vector<glm::vec3>{glm::vec3(2.0, 0.0, 0.0), glm::vec3(-3.0, 0.0, 0.0)}, sema::color::sgreen, 100, 0.01f, material0);
    sema::SPrimitive line0 = sema::generate_line(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(1.0f, 4.0f, 0.0f), sema::color::syellow, 20, 0.1f, material0);
    sema::SPrimitive triangle0 = sema::generate_triangle(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{1.0f, 0.0f, 0.0f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, material0);
    sema::SPrimitive rectangle0 = sema::generate_rectangle(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{1.0f, 0.0f, 0.0f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, material0);

    // 3D primitives
    sema::SPrimitive sphere0 = sema::generate_sphere(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{1.0f, 0.0f, 0.0f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, material0);
    sema::SPrimitive cylinder0 = sema::generate_cylinder(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{1.0f, 0.0f, 0.0f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, material0);
    sema::SPrimitive cube1 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{0.0f, 0.0f,  9.0f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::sred, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    sema::SPrimitive cube2 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{7.0f, 4.0f, -2.0f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::sblue, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    sema::SPrimitive cube3 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{0.8f, 0.5f,  5.2f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::scyan, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    sema::SPrimitive cube4 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{3.2f, 5.5f, -1.1f}, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::sgreen, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    sema::SPrimitive tile0 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, sema::STranslation{0.0f, 0.0f, -5.0f}, sema::SScale{50.0, 50.0f, 0.1f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::sgreen, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material2);
    
    sema::STranslation lightcube0_position = {0.0f, 0.0f,  0.0f};
    sema::SPrimitive lightcube0 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, lightcube0_position, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    sema::STranslation lightcube1_position = {-4.5f, -1.5f, 1.0f};
    sema::SPrimitive lightcube1 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, lightcube1_position, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    sema::STranslation lightcube2_position = {10.5f, -6.5f, 2.7f};
    sema::SPrimitive lightcube2 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, lightcube2_position, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    sema::STranslation lightcube3_position = {4.5f, 8.5f, 1.5f};
    sema::SPrimitive lightcube3 = sema::generate_cube(sema::STransform(sema::SRotation{0.0f, 0.0f, 0.0f}, lightcube3_position, sema::SScale{1.0f, 1.0f, 1.0f}, sema::SSize{1.0f, 1.0f, 1.0f}), sema::color::spink, glm::vec3{1.0f}, glm::vec3{1.0f}, glm::vec3{1.0f}, 0.5f, material1);
    // transform object
    // rotate_model(glm::radians(1.0f), glm::vec3(1.0f, 0.0f, 0.0f), tile0.model, tile0.vertices);

    OMeshBuffer line_mesh_buffer;
    line_mesh_buffer.offset = 0;
    line_mesh_buffer.materialID = 0;
    append_mesh(line_mesh_buffer, circle0);
    append_mesh(line_mesh_buffer, bcurve0);
    append_mesh(line_mesh_buffer, hcurve1);
    append_mesh(line_mesh_buffer, line0);
    line_mesh_buffer.indexed = (line_mesh_buffer.indices.size() > 0) ? true : false;

    OMeshBuffer shape_mesh_buffer;
    shape_mesh_buffer.offset = 0;
    shape_mesh_buffer.materialID = 1;
    append_mesh(shape_mesh_buffer, lightcube0);
    append_mesh(shape_mesh_buffer, lightcube1);
    append_mesh(shape_mesh_buffer, lightcube2);
    append_mesh(shape_mesh_buffer, lightcube3);
    append_mesh(shape_mesh_buffer, cube1);
    append_mesh(shape_mesh_buffer, cube2);
    append_mesh(shape_mesh_buffer, cube3);
    append_mesh(shape_mesh_buffer, cube4);
    append_mesh(shape_mesh_buffer, tile0);
    shape_mesh_buffer.indexed = (shape_mesh_buffer.indices.size() > 0) ? true : false;

    meshes.push_back(line_mesh_buffer);
    meshes.push_back(shape_mesh_buffer);

    GPULight light0;
    light0.direction = glm::vec4(1.0f);
    light0.position = glm::vec4{lightcube0_position.x, lightcube0_position.y, lightcube0_position.z, 1.0f};
    light0.ambient = glm::vec4{80.0f, 180.0f, 180.0f, 1.0f};
    light0.diffuse = glm::vec4{0.8f, 0.8f, 0.8f, 1.0f};
    light0.specular = glm::vec4{0.5f, 0.5f, 0.5f, 1.0f};
    light0.parameters = glm::vec4{0.1f, 30.0f, 20.0f, 0.0f};
    light0.options = glm::vec4{1.0f, 1.0f, 0.0f, 0.0f};
    
    GPULight light1;
    light1.direction = glm::vec4(1.0f);
    light1.position = glm::vec4{lightcube1_position.x, lightcube1_position.y, lightcube1_position.z, 1.0f};
    light1.ambient = glm::vec4{10.0f, 110.0f, 190.0f, 1.0f};
    light1.diffuse = glm::vec4{1.0f};
    light1.specular = glm::vec4{1.0f};
    light1.parameters = glm::vec4{0.1f, 15.0f, 10.0f, 0.0f};
    light1.options = glm::vec4{1.0f, 1.0f, 0.0f, 0.0f};
    
    GPULight light2;
    light2.direction = glm::vec4(1.0f);
    light2.position = glm::vec4{lightcube2_position.x, lightcube2_position.y, lightcube2_position.z, 1.0f};
    light2.ambient = glm::vec4{0.0f, 0.0f, 225.0f, 1.0f};
    light2.diffuse = glm::vec4{0.8f, 0.8f, 0.8f, 1.0f};
    light2.specular = glm::vec4{0.5f, 0.5f, 0.5f, 1.0f};
    light2.parameters = glm::vec4{0.1f, 7.0f, 1.0f, 0.0f};
    light2.options = glm::vec4{1.0f, 1.0f, 0.0f, 0.0f};
    
    GPULight light3;
    light3.direction = glm::vec4(1.0f);
    light3.position = glm::vec4{lightcube3_position.x, lightcube3_position.y, lightcube3_position.z, 1.0f};
    light3.ambient = glm::vec4{10.0f, 110.0f, 190.0f, 1.0f};
    light3.diffuse = glm::vec4{1.0f};
    light3.specular = glm::vec4{1.0f};
    light3.parameters = glm::vec4{0.1f, 5.2f, 0.91f, 0.0f};
    light3.options = glm::vec4{1.0f, 1.0f, 0.0f, 0.0f};

    lights.push_back(light0);
    lights.push_back(light1);
    lights.push_back(light2);
    lights.push_back(light3);

    VCamera camera0;
    camera0.position = glm::vec3(0.0f, 0.0f, 20.0f);
    camera0.front = glm::vec3{0.0f, 1.0f, 0.0f};
    camera0.up = glm::vec3{0.0f, 0.0f, 1.0f};
    camera0.speed_multiplier = 0.1f;
    camera0.speed = 10.5f;
    camera0.zoom = 1.0f;
    camera0.znear = 0.1f;
    camera0.zfar = 1000.0f;
    camera0.zoom_angle = glm::radians(45.0f);
    camera0.model = glm::mat4{1.0f};
    camera0.aspect = 4.0f / 3.0f;
    camera0.projection_mode = 0;
    cameras.push_back(camera0);

    std::default_random_engine rndEngine((unsigned)time(nullptr));
    std::uniform_real_distribution<float> rndDist(0.0f, 1.0f);
    std::vector<GPUParticle> iparticles(PARTICLE_COUNT);
    float r_scale = 0.25f; // 10.0f; // 0.25f
    float theta_scale = 2.5f; // 2.5f; // 2.5f
    float velocity_scale = 0.00025f; // 0.00025f
    for (auto& particle : iparticles)
    {
        float r = r_scale * sqrt(rndDist(rndEngine));
        float theta = rndDist(rndEngine) * theta_scale * PI;
        float x = r * cos(theta) * HEIGHT / WIDTH;
        float y = r * sin(theta);
        particle.position = glm::vec2(x, y);
        particle.velocity = glm::normalize(glm::vec2(x,y)) * velocity_scale;
        particle.color = glm::vec4(rndDist(rndEngine), rndDist(rndEngine), rndDist(rndEngine), 1.0f);
    }
    particles = iparticles;
}

void load_scene(uint32_t sceneID)
{

}

void save_scene()
{

}

void create_scene()
{

}

void update_scene()
{

}

void generate_scene_graph()
{

}

void create_mesh()
{

}

void create_camera()
{

}

void create_terrain()
{

}

void create_environment()
{

}

void create_light()
{

}

}; // namespace vulkan
