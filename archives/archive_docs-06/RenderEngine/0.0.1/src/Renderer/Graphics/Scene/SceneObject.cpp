/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "SceneObject.h"
#include "Logger.h"

using namespace RenderEngine;

SceneObject::SceneObject()
    : m_rotation(new Rotation())
    , m_position(new Vector(0, 0, 0))
    , m_scale(new Vector(1.0f, 1.0f, 1.0f))
    , m_color(new Color(1.0f, 0.0f, 0.0f))
{
    m_transform = new Transform();
    m_material = new Material(m_color);
}

SceneObject::~SceneObject()
{}

SceneObject::SceneObject(Transform transform)
{

}

SceneObject::SceneObject(Transform transform, Color color)
{

}

SceneObject::SceneObject(Transform transform, Material material)
{

}

SceneObject::SceneObject(Vector position, Rotation rotation, Vector scale)
{

}

SceneObject::SceneObject(Vector position, Rotation rotation, Vector scale, Color color)
{

}

SceneObject::SceneObject(Vector position, Rotation rotation, Vector scale, Material material)
{
    
}

void SceneObject::updateTransform(Transform transform)
{
    m_transform = transform;
}

void SceneObject::updatePosition(Vector position)
{
    m_position = position;
}

void SceneObject::updateRotation(Rotation rotation)
{
    m_rotation = rotation;
}

void SceneObject::updateScale(Vector scale)
{
    m_scale = scale;
}

void SceneObject::updateColor(Color color)
{
    m_color = color;
}

void SceneObject::updateMaterial(Material material)
{
    m_material = material;
}
