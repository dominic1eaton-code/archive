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
    m_eIDs.push_back(object->ID());
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
}

void VScene::load(std::vector<VertexShaderData>& vertices, std::vector<uint16_t>& indices, std::vector<GPUMeshData>& models, std::vector<GPUDirLight>& dirlights)
{
    // populate scene
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

    Square* tq = new Square(glm::vec3(0.0f));
    tq->rotate(glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    tq->translate(glm::vec3(0.0f, 0.0f, 1.0f));
    // meshbuffer->append(tq);
    // meshbuffer->append(sq0);
    // meshbuffer->append(sq1);
    // meshbuffer->append(sq2);

    /****************************************************************************************************************************************/
    // glm::mat4 model = glm::mat4(1.0f);
    // glm::mat4 transform = glm::translate(model, glm::vec3(1.5f, -0.5f, 0.0f));
    sq2->translate(glm::vec3(0.0f, 0.0f, 0.0f));
    sq2->rotate(glm::radians(0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    sq2->scale(glm::vec3(1.0, 1.0, 1.0));
    m_meshbuffer->append(cube0);
    m_meshbuffer->append(cube1);
    m_meshbuffer->append(cube2);
    m_meshbuffer->append(cube3);
    m_meshbuffer->append(cube4);

    //  lights
    // meshbuffer->append(new Cube(glm::vec3(5.0, 5.0f, 5.0f), glm::vec4(256.0f, 256.0f, 256.0f, 1.0), 0.2));
    // meshbuffer->append(new Cube(glm::vec3(-0.5f, 0.5f, 1.0f), glm::vec4(256.0f, 256.0f, 256.0f, 1.0), 0.2));

    // ground tiles
    // Square* stile = new Square(glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.2, 0.2, 1.0));
    Cube* tile = new Cube(glm::vec3(0.0f, 0.0f, -5.0f), glm::vec4(0.1f, 0.1f, 0.1f, 1.0), 0.2, glm::vec3(50.0, 50.0f, 0.1f));
    // tile->translate(glm::vec3(0.0f, 0.0f, -1.0f));
    m_meshbuffer->append(tile);

    // std::vector<glm::vec3> line = generateLine(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(0.0f, 0.0f, 1.0f), 10, 0.1f);
    // for (auto p : line)
    // {
    //     meshbuffer->append(new Cube(p, glm::vec4(0.0f, 0.0f, 100.0f, 1.0f), 0.1f));
    // }

    // std::vector<glm::vec3> ll = generateLine(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(0.0f, 1.0f, 0.0f), 10, 0.1f);
    // for (auto p : ll)
    // {
    //     meshbuffer->append(new Cube(p, glm::vec4(0.0f, 100.0f, 0.0f, 1.0f), 0.1f));
    // }
    
    // std::vector<glm::vec3> llx = generateLine(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(1.0f, 0.0f, 0.0f), 10, 0.1f);
    // for (auto p : llx)
    // {
    //     meshbuffer->append(new Cube(p, glm::vec4(100.0f, 0.0f, 0.0f, 1.0f), 0.1f));
    // }

    /****************************************************************************************************************************************/


    // GPUCamera camera0;
    // ubo.model = glm::rotate(glm::mat4(1.0f), tick * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    // camera0.model = glm::rotate(glm::mat4(1.0f), glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    // camera0.view = glm::lookAt(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    // camera0.proj = glm::perspective(glm::radians(45.0f), m_extent.width / (float) m_extent.height, 0.1f, 10.0f);
    // camera0.proj[1][1] *= -1;


    // Square* s3 = new Square(glm::vec3(1.5f, 0.5, 0.5), glm::vec3(0.2, 0.2, 1.0));
    // // square0->transform(glm::vec3(1.0f, 2.0f, 2.0f));
    // Square* square1 = new Square(glm::vec3(-0.3f, -.3f, -1.0f), glm::vec3(1.0f, 1.0f, 1.0f));
    // Square* square2 = new Square(glm::vec3(4.0f, 4.0f, -4.5f), glm::vec3(1.0f, 1.0f, 1.0f));
    // // square0->transform(glm::vec3(2.0f, 1.0f, 1.0f));
    // Triangle* triangle0 = new Triangle();


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

    // MeshBuffer* meshbuffer = new MeshBuffer();
    // meshbuffer->append(cube0);
    // meshbuffer->append(cube1);
    // meshbuffer->append(cube2);
    // meshbuffer->append(cube3);
    // meshbuffer->append(cube4);

    // Cube* cube4 = new Cube(glm::vec3(3.2f, 5.5f, -7.2f));
    // Cube* cube4 = new Cube(glm::vec3(3.2f, 5.5f, -7.2f));
    // Cube* cube4 = new Cube(glm::vec3(3.2f, 5.5f, -7.2f));
    // Cube* cube4 = new Cube(glm::vec3(3.2f, 5.5f, -7.2f));

    // meshbuffer->append(sq2);
    // std::vector<glm::vec3> line = generateLine(glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f), 5, 0.1);
    // for (auto p : line)
    // {
    //     meshbuffer->append(new Cube(p));
    // }

    // std::vector<glm::vec3> circle_points = generateCircle(1.0f, glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f), 200, 0.5f);
    // for (auto p : circle_points)
    // {
    //     meshbuffer->append(new Cube(p));
    // }

    // std::vector<glm::vec3> cp ={
    //     glm::vec3(2.0, 0.0, 0.0),
    //     glm::vec3(-3.0, 0.0, 0.0),
    //     glm::vec3(-4.0, 4.0, 0.0),
    //     glm::vec3(0.0, 5.0, 0.0),
    // };
    // std::vector<glm::vec3> bcurve = generateCubicBezier(cp, 100, 0.01f);
    // for (auto p : cp)
    // {
    //     meshbuffer->append(new Cube(p));
    // }
    // for (auto p : bcurve)
    // {
    //     meshbuffer->append(new Cube(p));
    // }

    std::vector<VertexShaderData> verts = m_meshbuffer->vertices(); // = square1->vertices();
    std::vector<uint16_t> inds = m_meshbuffer->indices(); // = square1->indices();

    vertices = verts;
    indices = inds;
    models = meshes;
    dirlights = dlights;
}