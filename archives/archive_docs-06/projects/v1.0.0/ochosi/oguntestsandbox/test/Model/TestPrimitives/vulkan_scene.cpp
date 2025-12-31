/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_scene.h"
#include <algorithm>

using namespace ogun;


template<typename T>
void MeshBuffer::append(T object)
{
    if (!m_empty) m_offset += object->vertices().size();
    for (auto vert : object->vertices())
    {
        m_vertices.push_back(vert);
    }
    for (auto ind : object->indices())
    {
        m_indices.push_back(ind + m_offset);
    }
    m_models.push_back(object->model());
    m_offsets.push_back(m_offset);
    m_vsizes.push_back(object->vertices().size());
    m_empty = false;
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

std::vector<VertexShaderData> generateCubicBezier(std::vector<glm::vec3> p, uint32_t numpoints, float stride = 0.1f)
{
    std::vector<glm::vec3> points;
    std::vector<VertexShaderData> vertices;
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    glm::vec2 texture{0.0f, 0.0f};
    if (p.size() == 4)
    {
        for (int i = 1; i < numpoints+1; i++)
        {
            // points.push_back(bezier(i*stride, p));
            // VertexShaderData vertex;
            // vertex.position = bezier(i*stride, p);
            // vertex.color = color;
            // vertex.texture = texture;
            // vertices.push_back(vertex);
            VertexShaderData v0;
            v0.position = bezier(i*stride, p);
            v0.color = color;
            v0.texture = texture;
            vertices.push_back(v0);
            
            VertexShaderData v1;
            v1.position = bezier((i+1)*stride, p);
            v1.color = color;
            v1.texture = texture;
            vertices.push_back(v1);
        } 
    }
    return vertices;
}

glm::vec3 circle(float t, float r, glm::vec3 p0)
{
    float x, y;
    x = p0.x + r*glm::cos(t);
    y = p0.y + r*glm::sin(t);
    return glm::vec3{x, y, 0.0f};
}

std::vector<VertexShaderData> generateCircle(float r, glm::vec3 p0, glm::vec3 normal, uint32_t numpoints, float stride = 0.2f)
{
    std::vector<glm::vec3> points;
    float x;
    float y;
    std::vector<VertexShaderData> vertices;
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    glm::vec2 texture{0.0f, 0.0f};
    for (int i = 1; i < numpoints+1; i++)
    {
        // x = p0.x + r*glm::cos(i*stride);
        // y = p0.y + r*glm::sin(i*stride);
        // points.push_back(glm::vec3(x, y, 0.0f));
        VertexShaderData v0;
        v0.position = circle(i*stride, r, p0);
        v0.color = color;
        v0.texture = texture;
        vertices.push_back(v0);
        
        VertexShaderData v1;
        v1.position = circle((i+1)*stride, r, p0);
        v1.color = color;
        v1.texture = texture;
        vertices.push_back(v1);
    }
    return vertices;
}

glm::vec3 line(float t, glm::vec3 axis, glm::vec3 p0)
{
    return glm::vec3(t)*axis*p0;
}

std::vector<VertexShaderData> generateLine(glm::vec3 p0, glm::vec3 axis, uint32_t numpoints, float stride = 0.2f)
{
    std::vector<VertexShaderData> vertices;
    std::vector<glm::vec3> points;
    // points.push_back(p0);
    glm::vec3 p = p0;
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    glm::vec2 texture{0.0f, 0.0f};
    for (int i = 1; i < numpoints+1; i++)
    {
        // p += (glm::vec3(i*stride))*axis;
        // points.push_back((glm::vec3(i*stride))*axis*p0);
        VertexShaderData v0;
        v0.position = line(i*stride, axis, p0);
        v0.color = color;
        v0.texture = texture;
        vertices.push_back(v0);
        
        VertexShaderData v1;
        v1.position = line((i+1)*stride, axis, p0);
        v1.color = color;
        v1.texture = texture;
        vertices.push_back(v1);
    }
    return vertices;
}

VScene::VScene()
{
    m_meshbuffer = new MeshBuffer();
}

void VScene::load(std::vector<VertexShaderData>& vertices, std::vector<uint16_t>& indices, std::vector<GPUMeshData>& models, std::vector<GPUDirLight>& dirlights)
{
    // populate scene
    Cube* cube0 = new Cube(glm::vec3(0.0f, 0.0f, 0.0f));
    Cube* cube1 = new Cube(glm::vec3(0.0f, 0.0f, 9.0f));
    Cube* cube2 = new Cube(glm::vec3(7.0f, 4.0f, -2.f));
    Cube* cube3 = new Cube(glm::vec3(0.8f, 0.5f, 5.2f));
    Cube* cube4 = new Cube(glm::vec3(3.2f, 5.5f, -1.1f));
    m_meshbuffer->append(cube0);
    m_meshbuffer->append(cube1);
    m_meshbuffer->append(cube2);
    m_meshbuffer->append(cube3);
    m_meshbuffer->append(cube4);

     std::vector<glm::vec3> cp ={
        glm::vec3(2.0, 0.0, 0.0),
        glm::vec3(-3.0, 0.0, 0.0),
        glm::vec3(-4.0, 4.0, 0.0),
        glm::vec3(0.0, 5.0, 0.0),
    };
    std::vector<VertexShaderData> bcurve = generateCubicBezier(cp, 100, 0.01f);
    std::vector<VertexShaderData> bline = generateLine(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(1.0f, 4.0f, 0.0f), 20, 0.1f);
    std::vector<VertexShaderData> bcircle = generateCircle(1.0f, glm::vec3(4.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f), 200, 0.5f);
    std::vector<VertexShaderData> bcircle2 = generateCircle(1.0f, glm::vec3(-4.0f, 2.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f), 200, 0.5f);
    std::vector<VertexShaderData> bcircle3 = generateCircle(2.5f, glm::vec3(-1.0f, 2.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f), 200, 0.5f);
    uint16_t s = bcurve.size();
    std::vector<VertexShaderData> verts = bcurve;// m_meshbuffer->vertices(); // = square1->vertices();
    std::vector<uint16_t> inds = {0};// m_meshbuffer->indices(); // = square1->indices();

    verts.insert( verts.end(), bcircle.begin(), bcircle.end());
    verts.insert( verts.end(), bcircle2.begin(), bcircle2.end());
    verts.insert( verts.end(), bcircle3.begin(), bcircle3.end());

    std::vector<GPUMeshData> meshes{};
    GPUMeshData mesh0;
    mesh0.model = glm::mat4(1.0f);
    meshes.push_back(mesh0);

    models = meshes;
    vertices = verts;
    indices = inds;
}