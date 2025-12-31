/**
 * @copyright
 * @brief
 * @note
 */
#pragma once
#ifndef sema_primitives_h
#define sema_primitives_h

#include "sema_math.h"
#include <vector>
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>

namespace sema
{

namespace color
{
    const SColorRGBA sred = SColorRGBA(1.0f, 0.0f, 0.0f, 1.0f);
    const SColorRGBA sgreen = SColorRGBA(0.0f, 1.0f, 0.0f, 1.0f);
    const SColorRGBA sblue = SColorRGBA(0.0f, 0.0f, 1.0f, 1.0f);
    const SColorRGBA sblack = SColorRGBA(0.0f, 0.0f, 0.0f, 1.0f);
    const SColorRGBA swhite = SColorRGBA(1.0f, 1.0f, 1.0f, 1.0f);
    const SColorRGBA syellow = SColorRGBA(1.0f, 1.0f, 0.0f, 1.0f);
    const SColorRGBA spink = SColorRGBA(1.0f, 0.0f, 1.0f, 1.0f);
    const SColorRGBA scyan = SColorRGBA(0.0f, 1.0f, 1.0f, 1.0f);
}

enum class VertexType
{
    MESH,
    PARTICLE
};

struct Vertex
{
    glm::vec4 color;
    glm::vec3 position;
    glm::vec3 normal;
    glm::vec3 tangent;
    glm::vec3 bitangent;
    glm::vec3 texture;
};

struct ParticleVertex
{
    glm::vec2 position;
    glm::vec2 velocity;
    glm::vec4 color;
};

struct SPoint
{

};

struct SSquare
{
    SSquare(STransform t, SColorRGBA c)
        : transform(t)
        , color(c)
        , model(1.0f)
        , side(0.5)
    {
        glm::vec3 tt = glm::vec3{transform.translation.x, transform.translation.y, transform.translation.z};
        glm::vec3 ss = glm::vec3{transform.scale.x, transform.scale.y, transform.scale.z};
        glm::vec4 cc = glm::vec4{color.r, color.g, color.b, color.a};
        // vertices = {
        //     {cc, {-side + tt.x, -side + tt.y, tt.z}, normal, {0.0f, 0.0f}},
        //     {cc, { side + tt.x, -side + tt.y, tt.z}, normal, {1.0f, 0.0f}},
        //     {cc, { side + tt.x,  side + tt.y, tt.z}, normal, {1.0f, 1.0f}},
        //     {cc, {-side + tt.x,  side + tt.y, tt.z}, normal, {0.0f, 1.0f}},
        // };
    };

    float side;
    glm::vec3 normal;
    SColorRGBA color;
    STransform transform;
    glm::mat4 model;
    std::vector<Vertex> vertices;
    std::vector<uint32_t> indices = {
        0, 1, 2, 2, 3, 0
    };
};

struct SCircle
{

};

struct SHexagon
{

};


struct SSphere
{

};

struct SPline
{

};

struct SLine
{

};

struct STriangle
{

};

struct SCube
{
    SCube(STransform t, SColorRGBA c)
        : transform(t)
        , color(c)
        , model(1.0f)
        , side(0.5)
    {
        glm::vec3 tt = glm::vec3{transform.translation.x, transform.translation.y, transform.translation.z};
        glm::vec3 ss = glm::vec3{transform.scale.x, transform.scale.y, transform.scale.z};
        glm::vec4 cc = glm::vec4{color.r, color.g, color.b, color.a};
        // vertices = {
        //     {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {0.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {1.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {1.0f, 1.0f}},
        //     {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {0.0f, 1.0f}},
            
        //     {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {0.0f, 0.0f}},
        //     {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {1.0f, 0.0f}},
        //     {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {1.0f, 1.0f}},
        //     {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {0.0f, 1.0f}},
            
        //     {cc, { side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {0.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {1.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {1.0f, 1.0f}},
        //     {cc, { side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {0.0f, 1.0f}},
            
        //     {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {0.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {1.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {1.0f, 1.0f}},
        //     {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {0.0f, 1.0f}},
            
        //     {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {0.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {1.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {1.0f, 1.0f}},
        //     {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, {0.0f, 1.0f}},
            
        //     {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {0.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {1.0f, 0.0f}},
        //     {cc, { side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {1.0f, 1.0f}},
        //     {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, {0.0f, 1.0f}},
        // };
    };

    float side;
    glm::vec3 normal;
    SColorRGBA color;
    STransform transform;
    glm::mat4 model;
    std::vector<Vertex> vertices;
    std::vector<uint32_t> indices = {
        0,  1,  2,  2,  3,  0,
        4,  5,  6,  6,  7,  4,
        8,  9,  10, 10, 11, 8,
        12, 13, 14, 14, 15, 12,
        16, 17, 18, 18, 19, 16,
        20, 21, 22, 22, 23, 20
    };
};

struct SCylinder
{

};

struct SRectangle
{

};

struct SPrimitive
{
    std::vector<Vertex> vertices;
    std::vector<uint32_t> indices;
    glm::mat4 model;
    std::vector<glm::vec4> color;
};

void transform_model(glm::mat4 trans, std::vector<Vertex>& vertices);
void scale_model(glm::vec3 scaling, glm::mat4& model, std::vector<Vertex>& vertices);
void translate_model(glm::vec3 translation, glm::mat4& model, std::vector<Vertex>& vertices);
void rotate_model(float rotation, glm::vec3 axis, glm::mat4& model, std::vector<Vertex>& vertices);

glm::vec3 hermite(float t, std::vector<glm::vec3> p, std::vector<glm::vec3> tp);
glm::vec3 bezier(float t, std::vector<glm::vec3> p);
glm::vec3 circle(float t, float r, glm::vec3 p0);
glm::vec3 line(float t, glm::vec3 axis, glm::vec3 p0);
glm::vec3 sphere(float t, float r, glm::vec3 p0);
glm::vec3 cylinder(float t, float r, glm::vec3 p0);
glm::vec3 polygon();

// ogun primitives
SPrimitive generate_circle(float r, glm::vec3 p0, glm::vec3 normal, SColorRGBA c, uint32_t numpoints, float stride = 0.2f, int32_t material = -1);
SPrimitive generate_line(glm::vec3 p0, glm::vec3 axis, SColorRGBA c, uint32_t numpoints, float stride = 0.2f, int32_t material = -1);
SPrimitive generate_bezier(std::vector<glm::vec3> p, SColorRGBA c, uint32_t numpoints, float stride = 0.1f, int32_t material = -1);
SPrimitive generate_hermite(std::vector<glm::vec3> p, std::vector<glm::vec3> t, SColorRGBA c, uint32_t numpoints, float stride = 0.1f, int32_t material = -1);
SPrimitive generate_triangle(STransform t, SColorRGBA c, int32_t material = -1);
SPrimitive generate_square(STransform t, SColorRGBA c, glm::vec3 normal, float side = 0.5f, int32_t material = -1);
SPrimitive generate_rectangle(STransform t, SColorRGBA c, int32_t material = -1);
SPrimitive generate_polygon(uint32_t degree, STransform t, SColorRGBA c, int32_t material = -1);
SPrimitive generate_hexagon(STransform t, SColorRGBA c, int32_t material = -1);
SPrimitive generate_plane();
SPrimitive generate_point();
SPrimitive generate_cube(STransform t, SColorRGBA c, glm::vec3 normal,  glm::vec3 tangent, glm::vec3 bitangent, float side = 0.5f, int32_t material = -1);
SPrimitive generate_sphere(STransform t, SColorRGBA c, int32_t material = -1);
SPrimitive generate_cylinder(STransform t, SColorRGBA c, int32_t material = -1);
SPrimitive generate_prism();
SPrimitive generate_cone();
SPrimitive generate_pyramid();
// ogun primitives

// ogun ui
SPrimitive create_widget();
SPrimitive create_menu();
SPrimitive create_button();
SPrimitive create_radio_button();
SPrimitive create_form();
SPrimitive create_dropdown_menu();
SPrimitive create_checkilst();
SPrimitive create_panel();
SPrimitive create_margin();
SPrimitive create_border();
SPrimitive create_padding();
SPrimitive create_header();
SPrimitive create_body();
SPrimitive create_content();
SPrimitive create_footer();
SPrimitive create_navigation();
SPrimitive create_background();
SPrimitive create_foreground();
void add_widget();
void add_text();
void update_widget();
void update_text();
// ogun ui

} // namespace sema


#endif // sema_primitives_h