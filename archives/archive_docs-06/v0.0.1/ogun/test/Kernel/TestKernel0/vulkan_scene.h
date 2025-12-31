/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_shader.h"


class Cube
{
public:
    Cube()
    : m_position(0.0f, 0.0f, 0.0f)
    , m_texture(1.0f, 1.0f)
    , m_scale(1.0f, 1.0f, 1.0f)
    , m_size(1.0f, 1.0f, 1.0f)
    , m_color(1.0f, 0.0f, 0.0f, 1.0f)
    {}

    virtual ~Cube(void) = default;

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

    std::vector<VertexShaderData> m_vertices = {
        {{-0.5f, -0.5f, 0.0f}, {1.0f, 0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
        {{ 0.5f, -0.5f, 0.0f}, {0.0f, 1.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
        {{ 0.5f,  0.5f, 0.0f}, {0.0f, 0.0f, 1.0f, 1.0f}, {1.0f, 1.0f}},
        {{-0.5f,  0.5f, 0.0f}, {1.0f, 1.0f, 1.0f, 1.0f}, {0.0f, 1.0f}},

        {{-0.5f, -0.5f, -0.5f}, {1.0f, 0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
        {{ 0.5f, -0.5f, -0.5f}, {0.0f, 1.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
        {{ 0.5f,  0.5f, -0.5f}, {0.0f, 0.0f, 1.0f, 1.0f}, {1.0f, 1.0f}},
        {{-0.5f,  0.5f, -0.5f}, {1.0f, 1.0f, 1.0f, 1.0f}, {0.0f, 1.0f}}
    };

    std::vector<uint16_t> m_indices = {
        0, 1, 2, 2, 3, 0,
        4, 5, 6, 6, 7, 4
    };

    // std::vector<VertexShaderData> m_vertices = {
    //     {{-((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}}, //{0.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
    //     {{ ((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
    //     {{ ((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 1.0f}},
    //     {{-((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}} //{0.0f, 0.0f, 1.0f}, {1.0f, 1.0f}}
    // };

    // std::vector<uint16_t> m_indices = {
    //     0, 1, 2, 2, 3, 0
    // };
};

class Square
{
public:

    Square(glm::vec3 position)
        : m_position(position)
        , m_texture(1.0f, 1.0f)
        , m_scale(1.0f, 1.0f, 1.0f)
        , m_size(1.0f, 1.0f, 1.0f)
        , m_color(1.0f, 0.0f, 0.0f, 1.0f)
    {
        m_vertices = {
            {{-((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {0.0f, 0.0f}}, //{0.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
            {{ ((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {1.0f, 0.0f}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
            {{ ((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {1.0f, 1.0f}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 1.0f}},
            {{-((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {0.0f, 1.0f}} //{0.0f, 0.0f, 1.0f}, {1.0f, 1.0f}}
        };
    }

    Square()
        : Square(glm::vec3(0.0f, 0.0f, 0.0f))
    {}

    virtual ~Square(void) = default;

    void transform(glm::vec3 position)
    {
        m_position = position;
        // m_vertices = {
        //     {{-((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {0.0f, 0.0f}}, //{0.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
        //     {{ ((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {1.0f, 0.0f}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
        //     {{ ((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {1.0f, 1.0f}}, //{0.0f, 0.0f, 1.0f}, {0.0f, 1.0f}},
        //     {{-((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, ((m_position.z + m_size.z) / 2) * m_scale.z}, {m_color.x, m_color.y, m_color.z, m_color.a}, {0.0f, 1.0f}} //{0.0f, 0.0f, 1.0f}, {1.0f, 1.0f}}
        // };
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

    // const std::vector<VertexShaderData> m_vertices = {
    //     {{-0.5f, -0.5f, 0.0f}, {1.0f, 0.0f, 1.0f, 1.0f}},
    //     {{ 0.5f, -0.5f, 0.0f}, {1.0f, 0.0f, 1.0f, 1.0f}},
    //     {{ 0.5f,  0.5f, 0.0f}, {1.0f, 0.0f, 1.0f, 1.0f}},
    //     {{-0.5f,  0.5f, 0.0f}, {1.0f, 0.0f, 1.0f, 1.0f}}
    // };

    std::vector<uint16_t> m_indices = {
        0, 1, 2, 2, 3, 0
    };
};



class Triangle
{
public:
    Triangle()
    : m_position(0.0f, 0.0f, 0.0f)
    , m_texture(1.0f, 1.0f)
    , m_scale(1.0f, 1.0f, 1.0f)
    , m_size(1.0f, 1.0f, 1.0f)
    , m_color(0.0f, 0.0f, 0.0f, 1.0f)
    {}

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

    const std::vector<VertexShaderData> m_vertices = {
        {{0.5f, -0.5f, 0.0f}, {1.0f, 1.0f, 0.0f, 1.0f}},
        {{0.5f,  0.5f, 0.0f}, {1.0f, 1.0f, 0.0f, 1.0f}},
        {{-0.5f, 0.5f, 0.0f}, {1.0f, 1.0f, 0.0f, 1.0f}},
    };

    // std::vector<VertexShaderData> m_vertices = {
    //     {{ ((m_position.x + m_size.x) / 2) * m_scale.x, -((m_position.y + m_size.y) / 2) * m_scale.y, /*((m_position.z + m_size.z) / 2) * m_scale.z*/ 0.0f}, {1.0f, 0.0f, 0.0f, 1.0f}, {0.0f, 0.0f, 1.0f}, {1.0f, 0.0f}},
    //     {{ ((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, /*((m_position.z + m_size.z) / 2) * m_scale.z*/ 0.0f}, {0.0f, 1.0f, 0.0f, 1.0f}, {0.0f, 0.0f, 1.0f}, {0.0f, 0.0f}},
    //     {{-((m_position.x + m_size.x) / 2) * m_scale.x,  ((m_position.y + m_size.y) / 2) * m_scale.y, /*((m_position.z + m_size.z) / 2) * m_scale.z*/ 0.0f}, {0.0f, 0.0f, 1.0f, 1.0f}, {0.0f, 0.0f, 1.0f}, {0.0f, 1.0f}}
    // };

    std::vector<uint16_t> m_indices = {
        0, 1, 2, 2, 3, 0
    };
};


// void append(std::vector<VertexShaderData>& vertices, std::vector<uint16_t>& indices)
// {
//     for (auto vert : vertices)
//     {
//         verts.push_back(vert);
//     }
    
//     for (auto ind : indices)
//     {
//         inds.push_back(ind);
//     }
// }

void load_scene(std::vector<VertexShaderData>& vertices, std::vector<uint16_t>& indices, std::vector<GPUMeshData>& models, std::vector<GPUDirLight>& dirlights)
{
    // populate scene
    std::vector<GPUCamera> cameras{};
    std::vector<GPUMeshData> meshes{};
    std::vector<GPUDirLight> dlights{};
    std::vector<GPULightData> lights{};
    
    // GPUCamera camera0;
    // ubo.model = glm::rotate(glm::mat4(1.0f), tick * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    // camera0.model = glm::rotate(glm::mat4(1.0f), glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    // camera0.view = glm::lookAt(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    // camera0.proj = glm::perspective(glm::radians(45.0f), m_extent.width / (float) m_extent.height, 0.1f, 10.0f);
    // camera0.proj[1][1] *= -1;

    GPUDirLight dlight0;
    dlight0.ambient = glm::vec4(1.0f);
    dlight0.diffuse = glm::vec4(1.0f);
    dlight0.specular = glm::vec4(1.0f);
    dlight0.direction = glm::vec4(1.0f, 1.0f, 1.0f, 1.0f);
    dlights.push_back(dlight0);

    GPUMeshData mesh0;
    // mesh0.model = glm::mat4(1.0f);
    mesh0.position = glm::vec4(0.0f);
    meshes.push_back(mesh0);

    Square* square0 = new Square(glm::vec3(0.0f, -0.5f, -2.0f));
    // square0->transform(glm::vec3(1.0f, 2.0f, 2.0f));
    
    Square* square1 = new Square(glm::vec3(-0.3f, -.3f, -1.0f));
    
    Square* square2 = new Square(glm::vec3(0.0f, -0.5f, -1.5f));
    // square0->transform(glm::vec3(2.0f, 1.0f, 1.0f));

    Triangle* triangle0 = new Triangle();
    
    Cube* cube0 = new Cube();

    // std::vector<VertexShaderData> verts = square0->vertices();
    // std::vector<uint16_t> inds = square0->indices();
    // vector1.insert( vector1.end(), vector2.begin(), vector2.end() ); // concat buffer data
    // vertices.insert( vertices.end(), square0->vertices().begin(), square0->vertices().end() );
    // indices.insert( indices.end(), square0->indices().begin(), square0->indices().end() );
    // std::vector<VertexShaderData> verts = triangle0->vertices();
    // std::vector<VertexShaderData> verts = cube0->vertices();
    // std::vector<uint16_t> inds = cube0->indices();

    
    // std::vector<VertexShaderData> verts = square0->vertices();
    // std::vector<uint16_t> inds = square0->indices();

    std::vector<VertexShaderData> verts = {}; // = square1->vertices();
    std::vector<uint16_t> inds = {}; // = square1->indices();

    for (auto vert: square0->vertices())
    {
        verts.push_back(vert);
    }
    for (auto ind: square0->indices())
    {
        inds.push_back(ind);
    }

    for (auto vert: square1->vertices())
    {
        verts.push_back(vert);
    }
    for (auto ind: square1->indices())
    {
        inds.push_back(ind + 4);
    }

    for (auto vert: square2->vertices())
    {
        verts.push_back(vert);
    }
    for (auto ind: square2->indices())
    {
        inds.push_back(ind + 8);
    }

    
    // verts.resize(verts.size() + square0->vertices().size());
    // inds.resize(inds.size() + square0->indices().size());

    // verts.insert(verts.end(), square0->vertices().begin(), square0->vertices().end());
    // inds.insert(inds.end(), square0->indices().begin(), square0->indices().end());

    vertices = verts;
    indices = inds;
    models = meshes;
    dirlights = dlights;
}
