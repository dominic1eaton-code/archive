/**
 * @copyright
 * @brief
 * @note
 */

#include "sema_primitives.h"
#include <assert.h>

namespace sema
{

void transform_model(glm::mat4 trans, std::vector<Vertex>& vertices)
{
    // model = trans;
    for (uint32_t v = 0; v < vertices.size(); v++)
    {
        glm::vec4 pos = trans * glm::vec4(vertices[v].position, 1.0f);
        vertices[v].position = glm::vec3(pos.x, pos.y, pos.z);
    }
}

void scale_model(glm::vec3 scaling, glm::mat4& model, std::vector<Vertex>& vertices)
{
    transform_model(glm::scale(model, glm::abs(scaling)), vertices);
};

void translate_model(glm::vec3 translation, glm::mat4& model, std::vector<Vertex>& vertices)
{
    transform_model(glm::translate(model, translation), vertices);
};

void rotate_model(float rotation, glm::vec3 axis, glm::mat4& model, std::vector<Vertex>& vertices)
{
    transform_model(glm::rotate(model, rotation, axis), vertices);
};

glm::vec3 line(float t, glm::vec3 axis, glm::vec3 p0)
{
    return glm::vec3(t)*axis*p0;
}

glm::vec3 circle(float t, float r, glm::vec3 p0)
{
    float x, y;
    x = p0.x + r*glm::cos(t);
    y = p0.y + r*glm::sin(t);
    return glm::vec3{x, y, 0.0f};
}

glm::vec3 bezier(float t, std::vector<glm::vec3> p)
{
    float a = glm::pow((1 - t), 3);
    float b = 3 * glm::pow((1 - t), 2) * t;
    float c = 3 * (1 - t) * glm::pow(t, 2);
    float d = glm::pow(t, 3);
    glm::vec3 hh = a * p[0] + b * p[1] + c * p[2] + d * p[3];
    return hh;
}

glm::vec3 hermite(float t, std::vector<glm::vec3> p, std::vector<glm::vec3> tp)
{
    float a = 2 * glm::pow((t), 3) - 3 * glm::pow((t), 2) + 1;
    float b = glm::pow((t), 3) - 2 * glm::pow((t), 2) + t;
    float c = glm::pow((t), 3) - glm::pow((t), 2);
    float d = -2 * glm::pow((t), 3) + 3 * glm::pow((t), 2);
    glm::vec3 hh = a * p[0] + b * tp[0] + c * tp[1] + d * p[1];
    return hh;
}

glm::vec3 polygon()
{
    glm::vec3 hh{0.0f};
    return hh;
}

SPrimitive generate_circle(float r, glm::vec3 p0, glm::vec3 normal, sema::SColorRGBA c, uint32_t numpoints, float stride, int32_t material)
{
    std::vector<glm::vec3> points;
    float x;
    float y;
    std::vector<Vertex> vertices;
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    glm::vec3 texture{0.0f, 0.0f, material};
    for (int i = 1; i < numpoints+1; i++)
    {
        Vertex v0;
        v0.position = circle(i*stride, r, p0);
        v0.color = glm::vec4{c.r, c.g, c.b, c.a};
        v0.texture = texture;
        v0.normal = normal;
        vertices.push_back(v0);
        
        Vertex v1;
        v1.position = circle((i+1)*stride, r, p0);
        v1.color = glm::vec4{c.r, c.g, c.b, c.a};
        v1.texture = texture;
        v0.normal = normal;
        vertices.push_back(v1);
    }
    
    SPrimitive primitive;
    primitive.vertices = vertices;
    primitive.indices = {};
    primitive.color.push_back(color);
    return primitive;
}

SPrimitive generate_line(glm::vec3 p0, glm::vec3 axis, sema::SColorRGBA c, uint32_t numpoints, float stride, int32_t material)
{
    std::vector<Vertex> vertices;
    std::vector<glm::vec3> points;
    glm::vec3 p = p0;
    glm::vec3 texture{0.0f, 0.0f, material};
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    glm::vec3 normal = {0.0f, 0.0f, 0.0f};
    for (int i = 1; i < numpoints+1; i++)
    {
        Vertex v0;
        v0.position = line(i*stride, axis, p0);
        v0.color = glm::vec4{c.r, c.g, c.b, c.a};
        v0.texture = texture;
        v0.normal = normal;
        vertices.push_back(v0);
        
        Vertex v1;
        v1.position = line((i+1)*stride, axis, p0);
        v1.color = glm::vec4{c.r, c.g, c.b, c.a};
        v1.texture = texture;
        v1.normal = normal;
        vertices.push_back(v1);
    }

    SPrimitive primitive;
    primitive.vertices = vertices;
    primitive.indices = {};
    primitive.color.push_back(color);
    return primitive;
}

SPrimitive generate_bezier(std::vector<glm::vec3> p, sema::SColorRGBA c, uint32_t numpoints, float stride, int32_t material)
{
    std::vector<glm::vec3> points;
    std::vector<Vertex> vertices;
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    glm::vec3 texture{0.0f, 0.0f, material};
    glm::vec3 normal = {0.0f, 0.0f, 0.0f};
    assert(p.size() == 4);
    if (p.size() == 4)
    {
        for (int i = 1; i < numpoints+1; i++)
        {
            Vertex v0;
            v0.position = bezier(i*stride, p);
            v0.color = color;
            v0.texture = texture;
            v0.normal = normal;
            vertices.push_back(v0);
            
            Vertex v1;
            v1.position = bezier((i+1)*stride, p);
            v1.color = color;
            v1.texture = texture;
            v1.normal = normal;
            vertices.push_back(v1);
        } 
    }

    SPrimitive primitive;
    primitive.vertices = vertices;
    primitive.indices = {};
    primitive.color.push_back(color);
    return primitive;
}

SPrimitive generate_hermite(std::vector<glm::vec3> p, std::vector<glm::vec3> t, sema::SColorRGBA c, uint32_t numpoints, float stride, int32_t material)
{

    std::vector<glm::vec3> points;
    std::vector<Vertex> vertices;
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    glm::vec3 texture{0.0f, 0.0f, material};
    glm::vec3 normal = {0.0f, 0.0f, 0.0f};
    assert(p.size() == 2);
    assert(t.size() == 2);
    if (p.size() == 4)
    {
        for (int i = 1; i < numpoints+1; i++)
        {
            Vertex v0;
            v0.position = hermite(i*stride, p, t);
            v0.color = color;
            v0.texture = texture;
            v0.normal = normal;
            vertices.push_back(v0);
            
            Vertex v1;
            v1.position = hermite((i+1)*stride, p, t);
            v1.color = color;
            v1.texture = texture;
            v1.normal = normal;
            vertices.push_back(v1);
        }
    }

    SPrimitive primitive;
    primitive.vertices = vertices;
    primitive.indices = {};
    primitive.color.push_back(color);
    return primitive;
}

SPrimitive generate_polygon(uint32_t degree, STransform t, SColorRGBA c, int32_t material)
{
    assert(degree > 1);
    std::vector<Vertex> vertices;
    // if (degree == 2) { return generate_line(); }
    // else if (degree == 3) { return generate_triangle(); }
    // else if (degree == 4) { return generate_rectangle(); }
    // else (degree > 4)
    if (degree  > 4)
    {
        polygon();
    }
    
    SPrimitive primitive;
    primitive.vertices = vertices;
    primitive.indices = {};
    // primitive.color.push_back(c);
    return primitive;
}

SPrimitive generate_triangle(sema::STransform t, sema::SColorRGBA c, int32_t material)
{
    SPrimitive primitive;
    return primitive;
}

SPrimitive generate_square(sema::STransform t, sema::SColorRGBA c, glm::vec3 normal, glm::vec3 tangent, glm::vec3 bitangent, float side, int32_t material)
{

    glm::vec3 tt = glm::vec3{t.translation.x, t.translation.y, t.translation.z};
    glm::vec3 ss = glm::vec3{t.scale.x, t.scale.y, t.scale.z};
    glm::vec4 cc = glm::vec4{c.r, c.g, c.b, c.a};
    std::vector<Vertex> vertices = {
        {cc, {-side + tt.x, -side + tt.y, tt.z}, normal, tangent, bitangent, {0.0f, 0.0f, material}},
        {cc, { side + tt.x, -side + tt.y, tt.z}, normal, tangent, bitangent, {1.0f, 0.0f, material}},
        {cc, { side + tt.x,  side + tt.y, tt.z}, normal, tangent, bitangent, {1.0f, 1.0f, material}},
        {cc, {-side + tt.x,  side + tt.y, tt.z}, normal, tangent, bitangent, {0.0f, 1.0f, material}},
    };

    std::vector<uint32_t> indices = {
        0, 1, 2, 2, 3, 0
    };

    SPrimitive primitive;
    primitive.vertices = vertices;
    primitive.indices = indices;
    primitive.color.push_back(cc);
    return primitive;
}

SPrimitive generate_rectangle(sema::STransform t, sema::SColorRGBA c, int32_t material)
{
    SPrimitive primitive;
    return primitive;
}

SPrimitive generate_hexagon(sema::STransform t, sema::SColorRGBA c, int32_t material)
{
    SPrimitive primitive;
    return primitive;
}

SPrimitive generate_cube(sema::STransform t, sema::SColorRGBA c, glm::vec3 normal, glm::vec3 tangent, glm::vec3 bitangent, float side, int32_t material)
{
    glm::vec3 tt = glm::vec3{t.translation.x, t.translation.y, t.translation.z};
    glm::vec3 ss = glm::vec3{t.scale.x, t.scale.y, t.scale.z};
    glm::vec4 cc = glm::vec4{c.r, c.g, c.b, c.a};
    std::vector<Vertex> vertices = {
        {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 1.0f, material}},
        {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 1.0f, material}},

        {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 0.0f, material}},
        {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 0.0f, material}},
        {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 1.0f, material}},
        {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 1.0f, material}},

        {cc, { side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 1.0f, material}},
        {cc, { side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 1.0f, material}},

        {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x,  side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 1.0f, material}},
        {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 1.0f, material}},

        {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 1.0f, material}},
        {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y,  side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 1.0f, material}},

        {cc, {-side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x,  side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 0.0f, material}},
        {cc, { side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {1.0f, 1.0f, material}},
        {cc, {-side * ss.x + tt.x, -side * ss.y + tt.y, -side * ss.z + tt.z}, normal, tangent, bitangent, {0.0f, 1.0f, material}},
    };
    
    std::vector<uint32_t> indices = {
        0,  1,  2,  2,  3,  0,
        4,  5,  6,  6,  7,  4,
        8,  9,  10, 10, 11, 8,
        12, 13, 14, 14, 15, 12,
        16, 17, 18, 18, 19, 16,
        20, 21, 22, 22, 23, 20
    };
    SPrimitive primitive;
    primitive.vertices = vertices;
    primitive.indices = indices;
    primitive.color.push_back(cc);
    return primitive;
}

SPrimitive generate_sphere(sema::STransform t, sema::SColorRGBA c, int32_t material)
{
    SPrimitive primitive;
    return primitive;
}

SPrimitive generate_cylinder(sema::STransform t, sema::SColorRGBA c, int32_t material)
{
    SPrimitive primitive;
    return primitive;
}

};