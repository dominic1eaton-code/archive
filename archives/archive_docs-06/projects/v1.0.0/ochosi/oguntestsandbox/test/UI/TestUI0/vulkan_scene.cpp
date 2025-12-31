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
    if (!m_empty) offset += object->vertices().size();
    for (auto vert : object->vertices())
    {
        m_vertices.push_back(vert);
    }
    for (auto ind : object->indices())
    {
        m_indices.push_back(ind + offset);
    }
    m_empty = false;
    m_offsets.push_back(offset);
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

void VScene::load(std::vector<VertexShaderData>& vertices, std::vector<uint16_t>& indices, std::vector<GPUMeshData>& models, std::vector<GPUDirLight>& dirlights)
{
    // populate scene
    MeshBuffer* meshbuffer = new MeshBuffer();
    std::vector<GPUCamera> cameras{};
    std::vector<GPUMeshData> meshes{};
    std::vector<GPUDirLight> dlights{};
    std::vector<GPULightData> lights{};
    
    GPUDirLight dlight0;
    dlight0.ambient = glm::vec4(1.0f);
    dlight0.diffuse = glm::vec4(1.0f);
    dlight0.specular = glm::vec4(1.0f);
    dlight0.direction = glm::vec4(2.0f, 1.0f, 2.0f, 1.0f);
    dlights.push_back(dlight0);

    GPUMeshData mesh0;
    // mesh0.model = glm::mat4(1.0f);
    mesh0.model = glm::mat4(1.0f);
    meshes.push_back(mesh0);
    Triangle* tri0 = new Triangle(glm::vec3(0.0, 0.0, 0.0));
    Square* sq0 = new Square(glm::vec3(1.2f, 1.0f, 1.5f), glm::vec3(0.2, 0.2, 1.0));
    Square* sq1 = new Square(glm::vec3(0.5f, 0.5f, 1.1f), glm::vec3(0.2, 0.2, 1.0));
    Square* sq2 = new Square(glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.2, 0.2, 1.0));

    Cube* cube0 = new Cube(glm::vec3(0.0f, 0.0f, 0.0f));
    Cube* cube1 = new Cube(glm::vec3(0.0f, 0.0f, 9.0f));
    Cube* cube2 = new Cube(glm::vec3(7.0f, 4.0f, -2.f));
    Cube* cube3 = new Cube(glm::vec3(0.8f, 0.5f, 5.2f));
    Cube* cube4 = new Cube(glm::vec3(3.2f, 5.5f, -1.1f));

    // Square* tq = new Square(glm::vec3(0.577f, 0.0f, 0.0f), glm::vec3(0.5f, 2.5f, 1.0f));
    Square* tq = new Square(glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(1.0f, 1.0f, 0.0f));
    // tq->scale(glm::vec3(1.0f, .5f, 1.0f));
    // tq->rotate(glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    // tq->translate(glm::vec3(0.0f, 0.0f, 1.0f));
    // tq->rotate(glm::radians(90.0f), glm::vec3(0.0f, 0.0f,1.0f));
    meshbuffer->append(tq);
    // meshbuffer->append(sq0);
    // meshbuffer->append(sq1);
    // meshbuffer->append(sq2);

    
    // Square* tq2 = new Square(glm::vec3(0.0f,  0.6, 0.0f));
    // meshbuffer->append(tq2);

    
    // Square* tq3 = new Square(glm::vec3(-0.5f, 0.0f, 0.0f));
    // meshbuffer->append(tq3);

    /****************************************************************************************************************************************/
    // glm::mat4 model = glm::mat4(1.0f);
    // glm::mat4 transform = glm::translate(model, glm::vec3(1.5f, -0.5f, 0.0f));
    sq2->translate(glm::vec3(0.0f, 0.0f, 0.0f));
    sq2->rotate(glm::radians(0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    sq2->scale(glm::vec3(1.0, 1.0, 1.0));

    std::vector<VertexShaderData> verts = meshbuffer->vertices(); // = square1->vertices();
    std::vector<uint16_t> inds = meshbuffer->indices(); // = square1->indices();

    vertices = verts;
    indices = inds;
    models = meshes;
    dirlights = dlights;
}