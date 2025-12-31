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
    // environments
    // Environment* environment = createSceneObject<Environment>("environment");

    // terrains
    // Terrain* terrain = createSceneObject<Terrain>("terrains");
    
    // cameras
    // Camera* camera0  = createSceneObject<Camera>("camera0");
    Camera* camera0  = new Camera("camera0");
    camera0->changeLocation(Vector(4.0f, 4.0f, 1.0f));
    camera0->changeRotation(Rotation(0.0f, 0.0f, 0.0f));
    camera0->changeScale(Vector(1.0f, 1.0f, 1.0f));
    camera0->changeColor(Color(0.0f, 1.0f, 0.0f));

           // lights
    // Light* light0 = createSceneObject<Light>("light0");
    // Light* light1 = createSceneObject<Light>("light1");
    Light* light0 = new Light("light0");
    Light* light1 = new Light("light1");

    light0->changeLocation(Vector(0.0f, 0.0f, -2.0));
    light0->changeRotation(Rotation(0.0f, 0.0f, 0.0f));
    light0->changeScale(Vector(1.0f, 1.0f, 1.0f));
    light0->changeColor(Color(0.9f, 0.9f, 0.9f));

    light1->changeLocation(Vector(0.0f, 0.0f, 2.0));
    light1->changeRotation(Rotation(0.0f, 0.0f, 0.0f));
    light1->changeScale(Vector(1.0f, 1.0f, 1.0f));
    light1->changeColor(Color(0.9f, 0.9f, 0.9f));

    // meshes
    // Mesh* cube0 = createSceneObject<Mesh>("cube0");
    // Mesh* cube1 = createSceneObject<Mesh>("cube1");
    // Mesh* cube2 = createSceneObject<Mesh>("cube2");
    // Mesh* cube3 = createSceneObject<Mesh>("cube3");
    Mesh* cube0 = new Mesh("cube0");
    Mesh* cube1 = new Mesh("cube1");
    Mesh* cube2 = new Mesh("cube2");
    Mesh* cube3 = new Mesh("cube3");

    cube0->changeLocation(Vector(2.0f, 0.0f, 0.0));
    cube0->changeRotation(Rotation(0.0f, 0.0f, 0.0f));
    cube0->changeScale(Vector(1.0f, 1.0f, 1.0f));
    cube0->changeColor(Color(1.0f, 0.0f, 0.0f));

    cube1->changeLocation(Vector(-2.0f, 0.0f, 0.0));
    cube1->changeRotation(Rotation(0.0f, 0.0f, 0.0f));
    cube1->changeScale(Vector(1.0f, 1.0f, 1.0f));
    cube1->changeColor(Color(0.0f, 1.0f, 0.0f));

    cube2->changeLocation(Vector(0.0f, 2.0f, 0.0));
    cube2->changeRotation(Rotation(0.0f, 0.0f, 0.0f));
    cube2->changeScale(Vector(1.0f, 1.0f, 1.0f));
    cube2->changeColor(Color(0.0f, 0.0f, 1.0f));

    cube3->changeLocation(Vector(0.0f, -2.0f, 0.0));
    cube3->changeRotation(Rotation(0.0f, 0.0f, 0.0f));
    cube3->changeScale(Vector(1.0f, 1.0f, 1.0f));
    cube3->changeColor(Color(1.0f, 1.0f, 0.0f));

    // register scene objects
    registerSceneObject<Camera>(camera0);
}

void TestScene0::update(float tick)
{
    // static auto startTime = std::chrono::high_resolution_clock::now();
    // auto currentTime = std::chrono::high_resolution_clock::now();
    // float time = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();
    // uint8_t rotationDirection = -1;
    // float tick = time; // float update = 81;
 
    m_cameras[0].model = glm::rotate(glm::mat4(1.0f), tick * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    m_cameras[0].view = glm::lookAt(cameraData.position, glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    m_cameras[0].proj = glm::perspective(glm::radians(45.0f), m_swapChainExtent.width / (float) m_swapChainExtent.height, 0.1f, 10.0f);
    m_cameras[0].proj[1][1] *= -1;

    m_cameras["camera"]->rotate(Rotation(0.0f, 0.0f, 90.0f));
}

