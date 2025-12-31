/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#pragma once

#ifndef vulkan_scene_h
#define vulkan_scene_h

#include "vulkan_gpu.h"

#include "Ogun/Core/Vertex.h"

namespace ogun
{

class Cube
{
public:

    Cube(glm::vec3 position)
        : Cube(position, glm::vec4(0.1f, 0.1f, 0.1f, 1.0f), 0.5f, glm::vec3(1.0f))
    {}
    
    Cube(glm::vec3 position, float side)
        : Cube(position, glm::vec4(0.1f, 0.1f, 0.1f, 1.0f), side, glm::vec3(1.0f))
    {}

    Cube(glm::vec3 position, glm::vec4 color, float side)
        : Cube(position, glm::vec4(0.1f, 0.1f, 0.1f, 1.0f), side, glm::vec3(1.0f))
    {}

    Cube(glm::vec3 position, glm::vec4 color, glm::vec3 scale)
        : Cube(position, glm::vec4(0.1f, 0.1f, 0.1f, 1.0f), 0.5F, scale)
    {}

    Cube(glm::vec3 position, glm::vec4 color, float side, glm::vec3 scale)
        : m_position(position)
        , m_texture(1.0f, 1.0f)
        , m_scale(scale)
        , m_size(1.0f, 1.0f, 1.0f)
        , m_color(color)
        , m_side(side)
        , m_model(glm::mat4(1.0f))
    {
        m_vertices = {
            {{-m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {0.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {1.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {1.0f, 1.0f}},
            {{-m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {0.0f, 1.0f}},

            {{-m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {0.0f, 0.0f}},
            {{-m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {1.0f, 0.0f}},
            {{-m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {1.0f, 1.0f}},
            {{-m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {0.0f, 0.0f}},

            {{ m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {0.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {1.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {1.0f, 1.0f}},
            {{ m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {0.0f, 1.0f}},

            {{-m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {0.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {1.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {1.0f, 1.0f}},
            {{-m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {0.0f, 1.0f}},

            {{-m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {0.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {1.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {1.0f, 1.0f}},
            {{-m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y,  m_side*m_scale.z + m_position.z}, m_color, {0.0f, 1.0f}},

            {{-m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {0.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x,  m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {1.0f, 0.0f}},
            {{ m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {1.0f, 1.0f}},
            {{-m_side*m_scale.x + m_position.x, -m_side*m_scale.y + m_position.y, -m_side*m_scale.z + m_position.z}, m_color, {0.0f, 1.0f}},
        };
    }

    Cube()
        : Cube(glm::vec3(0.0f, 0.0f, 0.0f))
    {}

    virtual ~Cube(void) = default;

    glm::mat4 model() const { return m_model; }

    std::vector<VertexShaderData> vertices() const { return m_vertices; }
    
    std::vector<uint16_t> indices() const { return m_indices; }

    uint32_t ID() const { return m_eID; }

    void scale(glm::vec3 scaling)
    {
        transform(glm::scale(m_model, glm::abs(scaling)));
    };

    void translate(glm::vec3 translation)
    {
        transform(glm::translate(m_model, translation));
    };
    
    void rotate(float rotation, glm::vec3 axis)
    {
        transform(glm::rotate(m_model, rotation, axis));
    };

private:

    void transform(glm::mat4 trans)
    {
        m_model = trans;
        for (uint32_t v = 0; v < m_vertices.size(); v++)
        {
            glm::vec4 pos = m_model * glm::vec4(m_vertices[v].position, 1.0f);
            m_vertices[v].position = glm::vec3(pos.x, pos.y, pos.z);
        }
    }

    glm::mat4 m_model; 

    float m_side = 1.0f;
    
    glm::vec2 m_texture;
    
    glm::vec3 m_position;
    
    glm::vec4 m_color;
    
    glm::vec3 m_scale;

    glm::vec3 m_size;

    uint32_t m_eID;
    
    std::vector<VertexShaderData> m_points;

    std::vector<VertexShaderData> m_vertices;

    std::vector<uint16_t> m_indices = {
        0,  1,  2,  2,  3,  0,
        4,  5,  6,  6,  7,  4,
        8,  9,  10, 10, 11, 8,
        12, 13, 14, 14, 15, 12,
        16, 17, 18, 18, 19, 16,
        20, 21, 22, 22, 23, 20
    };
};

class Square
{
public:

    Square(glm::vec3 position)
        : Square(position, glm::vec3(1.0f), 0.5f)
    {}

    Square(glm::vec3 position, glm::vec3 scale)
        : Square(position, scale, 0.5f)
    {}

    Square(glm::vec3 position, glm::vec3 scale, float side)
        : m_position(position)
        , m_scale(scale)
        , m_texture(1.0f, 1.0f)
        , m_size(1.0f, 1.0f, 1.0f)
        , m_color(1.0f, 0.0f, 0.0f, 1.0f)
        , m_model(1.0f)
        , m_side(side)
    {
        glm::mat4 translationMatrix = glm::translate(m_model, m_position);
        m_vertices = {
            {{-m_side + m_position.x, -m_side + m_position.y, m_position.z}, {1.0f, 0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
            {{ m_side + m_position.x, -m_side + m_position.y, m_position.z}, {0.0f, 1.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
            {{ m_side + m_position.x,  m_side + m_position.y, m_position.z}, {0.0f, 0.0f, 1.0f, 1.0f}, {1.0f, 1.0f}},
            {{-m_side + m_position.x,  m_side + m_position.y, m_position.z}, {1.0f, 1.0f, 1.0f, 1.0f}, {0.0f, 1.0f}},
            // {{-((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {0.0f, 0.0f}}, //{0.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
            // {{ ((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {1.0f, 0.0f}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
            // {{ ((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {1.0f, 1.0f}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 1.0f}},
            // {{-((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {0.0f, 1.0f}} //{0.0f, 0.0f, 1.0f}, {1.0f, 1.0f}}
        };
        
        // std::vector<uint16_t> m_indices = {
        //     0, 1, 2, 2, 3, 0
        // };
    }

    Square()
        : Square(glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(1.0f, 1.0f, 1.0f))
    {}

    virtual ~Square(void) = default;

    void scale(glm::vec3 scaling)
    {
        transform(glm::scale(m_model, glm::abs(scaling)));
    };

    void translate(glm::vec3 translation)
    {
        transform(glm::translate(m_model, translation));
    };
    
    void rotate(float rotation, glm::vec3 axis)
    {
        transform(glm::rotate(m_model, rotation, axis));
    };

    void transform(glm::mat4 trans)
    {
        m_model = trans;
        for (uint32_t v = 0; v < m_vertices.size(); v++)
        {
            glm::vec4 pos = m_model * glm::vec4(m_vertices[v].position, 1.0f);
            m_vertices[v].position = glm::vec3(pos.x, pos.y, pos.z);
        }
    }

    std::vector<VertexShaderData> vertices() const { return m_vertices; }
    
    std::vector<uint16_t> indices() const { return m_indices; }

private:
    float m_side;

    glm::mat4 m_model; 

    glm::vec2 m_texture;
    
    glm::vec3 m_position;
    
    glm::vec4 m_color;
    
    glm::vec3 m_scale;

    glm::vec3 m_size;
    
    std::vector<VertexShaderData> m_points;

    std::vector<VertexShaderData> m_vertices;

    std::vector<uint16_t> m_indices = {
        0, 1, 2, 2, 3, 0
    };
};

class Triangle
{
public:
    
    Triangle()
        : Triangle(glm::vec3(0.0f))
    {}

    Triangle(glm::vec3 position)
    : m_position(0.0f, 0.0f, 0.0f)
    , m_texture(1.0f, 1.0f)
    , m_scale(1.0f, 1.0f, 1.0f)
    , m_size(1.0f, 1.0f, 1.0f)
    , m_color(0.0f, 0.0f, 0.0f, 1.0f)
    {
        float m_side = 0.5f;
        m_vertices = {
            {{ m_side + m_position.x, -m_side + m_position.y, m_position.z}, {1.0f, 1.0f, 0.0f, 1.0f}, {1, 0}},
            {{ m_side + m_position.x,  m_side + m_position.y, m_position.z}, {1.0f, 1.0f, 0.0f, 1.0f}, {0, 1}},
            {{-m_side + m_position.x,  m_side + m_position.y, m_position.z}, {1.0f, 1.0f, 0.0f, 1.0f}, {1, 1}},
        };
        
        m_indices = {};
        // m_indices = {
        //     0, 1, 2
        // };
    }

    virtual ~Triangle(void) = default;

    void transform(glm::vec3 position)
    {
        m_position = position;
    };

    std::vector<VertexShaderData> vertices() const { return m_vertices; }
    
    std::vector<uint16_t> indices() const { return m_indices; }

private:
    
    glm::vec2 m_texture;
    
    glm::vec3 m_position;
    
    glm::vec4 m_color;
    
    glm::vec3 m_scale;

    glm::vec3 m_size;
    
    std::vector<VertexShaderData> m_points;

    std::vector<VertexShaderData> m_vertices;

    std::vector<uint16_t> m_indices;
};

class MeshBuffer
{
public:
    MeshBuffer()
        : m_vertices({})
        , m_indices({})
        , m_offset(0)
    {}

    virtual ~MeshBuffer(void) = default;

    void updateModel(glm::mat4 model, uint32_t index)
    {
        m_models[index] = model;
    }

    void updateVertex(VertexShaderData vertex, uint32_t index)
    {
        m_vertices[index] = vertex;
    }

    std::vector<uint32_t> vsizes() const { return m_vsizes; }

    std::vector<VertexShaderData> vertices() const { return m_vertices; }

    std::vector<uint16_t> indices() const { return m_indices; }

    std::vector<glm::mat4> models() const { return m_models; }

    std::vector<uint32_t> offsets() const { return m_offsets; }

    std::vector<uint32_t> IDs() const { return m_eIDs; }

    bool m_empty = true;

    template<typename T>
    void append(T object);

    // void remove();

    // void insert();

private:
    std::vector<VertexShaderData> m_vertices;

    std::vector<uint16_t> m_indices;

    std::vector<glm::mat4> m_models;

    std::vector<uint32_t> m_offsets;

    std::vector<uint32_t> m_vsizes;
    
    std::vector<uint32_t> m_eIDs;

    uint32_t m_offset;
};

class VScene
{
public:
    VScene();
    virtual ~VScene(void) = default;

    void load(std::vector<VertexShaderData>& vertices, std::vector<uint16_t>& indices, std::vector<GPUMeshData>& models, std::vector<GPUDirLight>& dirlights);

    MeshBuffer* meshbuffer() const { return m_meshbuffer; }

private:
    // std::vector<MeshBuffer*> m_meshBuffers;

    MeshBuffer* m_meshbuffer;

};


class VMesh
{
public:
    VMesh() = default;
    virtual ~VMesh(void) = default;

private:
    
    glm::vec3 m_color;
    
    glm::vec3 m_texture;

};

struct Rotation
{
    float m_roll;
    
    float m_pitch;
    
    float m_yaw;
};

class VCamera
{
public:
    VCamera() = default;
    virtual ~VCamera(void) = default;

private:
    GPUCamera gcamera;

    glm::mat4 m_model;

    glm::vec3 m_position;

    Rotation m_rotation;
};


}; // namespace ogun

#endif // vulkan_scene_h