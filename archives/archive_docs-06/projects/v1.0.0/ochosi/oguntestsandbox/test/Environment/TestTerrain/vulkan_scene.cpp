/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_terrain.h"
// #include "vulkan_model.h"
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

std::vector<glm::vec3> generateCubicBezier(std::vector<glm::vec3> p, uint32_t numpoints, float stride = 0.1f)
{
    std::vector<glm::vec3> points;
    if (p.size() == 4)
    {
        for (int i = 1; i < numpoints+1; i++)
        {
            points.push_back(bezier(i*stride, p));
        } 
    }
    return points;
}

std::vector<glm::vec3> generateCircle(float r, glm::vec3 p0, glm::vec3 normal, uint32_t numpoints, float stride = 0.2f)
{
    std::vector<glm::vec3> points;
    float x;
    float y;
    for (int i = 1; i < numpoints+1; i++)
    {
        x = p0.x + r*glm::cos(i*stride);
        y = p0.y + r*glm::sin(i*stride);
        points.push_back(glm::vec3(x, y, 0.0f));
    }
    return points;
}

std::vector<glm::vec3> generateLine(glm::vec3 p0, glm::vec3 axis, uint32_t numpoints, float stride = 0.2f)
{
    std::vector<glm::vec3> points;
    // points.push_back(p0);
    glm::vec3 p = p0;
    for (int i = 1; i < numpoints+1; i++)
    {
        // p += (glm::vec3(i*stride))*axis;
        points.push_back((glm::vec3(i*stride))*axis*p0);
    }
    return points;
}

VScene::VScene()
{
    m_meshbuffer = new MeshBuffer();
    m_terrain = new VTerrain();
}

void VScene::load(std::vector<TVertex>& vertices, std::vector<uint16_t>& indices, std::vector<GPUMeshData>& models, std::vector<GPUDirLight>& dirlights,
                  glm::vec2 terrainHeightMapExtent)
{
    // populate scene
    // meshes
    // Cube* cube0 = new Cube(glm::vec3(0.0f, 0.0f, 0.0f));
    // Cube* cube1 = new Cube(glm::vec3(0.0f, 0.0f, 9.0f));
    // Cube* cube2 = new Cube(glm::vec3(7.0f, 4.0f, -2.f));
    // Cube* cube3 = new Cube(glm::vec3(0.8f, 0.5f, 5.2f));
    // Cube* cube4 = new Cube(glm::vec3(3.2f, 5.5f, -1.1f));
    // m_meshbuffer->append(cube0);
    // m_meshbuffer->append(cube1);
    // m_meshbuffer->append(cube2);
    // m_meshbuffer->append(cube3);
    // m_meshbuffer->append(cube4);
    
    // ground tiles
    // Cube* tile = new Cube(glm::vec3(0.0f, 0.0f, -5.0f), glm::vec4(0.1f, 0.1f, 0.1f, 1.0), 0.2, glm::vec3(50.0, 50.0f, 0.1f));
    // m_meshbuffer->append(tile);

    // terrain
    // m_terrain->loadHeightMap(terrainHeightMapExtent.x, terrainHeightMapExtent.y);
    uint32_t terrain_quad_multiplier = 600u;
    uint32_t terrain_width = 1u;
    uint32_t terrain_height= 1u;
    m_terrain->loadHeightMap(terrain_quad_multiplier*terrain_width, terrain_quad_multiplier*terrain_height);
    std::vector<TVertex> verts = m_terrain->vertices();

    // std::vector<TVertex> verts = m_meshbuffer->vertices(); // = square1->vertices();
    std::vector<uint16_t> inds = {0}; //m_meshbuffer->indices(); // = square1->indices();

    vertices = verts;
    indices = inds;
}