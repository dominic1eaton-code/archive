/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "TestScene0.h"
#include "Logger.h"

using namespace RenderEngine;

TestScene0::TestScene0()
{}

TestScene0::TestScene0()
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
}

TestScene0::~TestScene0()
{
    vkDestroyDevice(m_swapChain, nullptr);
}

template<class ReturnType>
ReturnType* createSceneObject(std::string name)
{

}

void TestScene0::setup()
{
    // add to scene object vectors
    createSceneObject<Camera>(camera0);
    createSceneObject<Light>(light0);
    createSceneObject<Light>(light1);
    createSceneObject<Mesh>(cube0);
    createSceneObject<Mesh>(cube1);
    createSceneObject<Mesh>(cube2);
    createSceneObject<Mesh>(cube3);

    
    // environments
    Environment* environment = new Environment();

    // terrains
    Terrain* terrain = new Terrain();
    
    // cameras
    Camera* camera0  = new Camera(Vector(4.0f, 4.0f, 1.0f), Rotation(0.0f, 0.0f, 0.0f), Vector(1.0f, 1.0f, 1.0f), Color(0.0f, 1.0f, 0.0f));

    // lights
    Light* light0 = new Light(Vector(0.0f, 0.0f, 0.0f), Rotation(0.0f, 0.0f, 0.0f), Vector(1.0f, 1.0f, 1.0f), Color(0.9f, 0.9f, 0.9f));
    Light* light1 = new Light(Vector(0.0f, 0.0f, 0.0f), Rotation(0.0f, 0.0f, 0.0f), Vector(1.0f, 1.0f, 1.0f), Color(0.0f, 1.0f, 0.0f));

    // meshes
    Mesh* cube0 = new Cube(Vector(1.0f, 1.0f, 0.0f), Rotation(0.0f, 0.0f, 0.0f), Vector(1.0f, 1.0f, 1.0f), Color(0.0f, 1.0f, 0.0f));
    Mesh* cube1 = new Cube(Vector(1.0f, 1.0f, 0.0f), Rotation(0.0f, 0.0f, 0.0f), Vector(1.0f, 1.0f, 1.0f), Color(0.0f, 1.0f, 0.0f));
    Mesh* cube2 = new Cube(Vector(1.0f, 1.0f, 0.0f), Rotation(0.0f, 0.0f, 0.0f), Vector(1.0f, 1.0f, 1.0f), Color(0.0f, 1.0f, 0.0f));
    Mesh* cube3 = new Cube(Vector(1.0f, 1.0f, 0.0f), Rotation(0.0f, 0.0f, 0.0f), Vector(1.0f, 1.0f, 1.0f), Color(0.0f, 1.0f, 0.0f));

}

void TestScene0::update(float tick)
{
    // static auto startTime = std::chrono::high_resolution_clock::now();
    // auto currentTime = std::chrono::high_resolution_clock::now();
    // float time = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();
    // uint8_t rotationDirection = -1;
    // float tick = time; // float update = 81;

    m_cameras[0].position = glm::vec3(4.0f, 4.0f, 1.0f);
    m_cameras[0].model = glm::rotate(glm::mat4(1.0f), tick * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    m_cameras[0].view = glm::lookAt(cameraData.position, glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    m_cameras[0].proj = glm::perspective(glm::radians(45.0f), m_swapChainExtent.width / (float) m_swapChainExtent.height, 0.1f, 10.0f);
    m_cameras[0].proj[1][1] *= -1;

    camera0.rotate(Rotation(0.0f, 0.0f, 90.0f));
}

