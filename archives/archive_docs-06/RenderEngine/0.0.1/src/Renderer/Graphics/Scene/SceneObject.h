/**
 * @brief   Default top level frame buffer for render application
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#pragma once

#ifndef SCENEOBJECT_H
#define SCENEOBJECT_H

#include "VulkanDefines.h"
#include <string>

// forward declerations
namespace LoggingTool { class Logger; }

namespace RenderEngine
{
    class Transform;
    class Vector;
    class Rotation;
    class Material;
    class Color;

    class RENGINE_API SceneObject
    {
    public:
        SceneObject();
        SceneObject(Transform transform);
        SceneObject(Transform transform, Color color);
        SceneObject(Transform transform, Material material);
        SceneObject(Vector position, Rotation rotation, Vector scale);
        SceneObject(Vector position, Rotation rotation, Vector scale, Color color);
        SceneObject(Vector position, Rotation rotation, Vector scale, Material material);
        SceneObject();
        virtual ~SceneObject(void);

        /* */
        void updateTransform(Transform transform);

        /* */
        void updatePosition(Vector position);

        /* */
        void updateRotation(Rotation rotation);

        /* */
        void updateScale(Vector scale);

        /* */
        void updateColor(Color color);

        /* */
        void updateMaterial(Material material);

    private:
        /* */
        std::string m_name;

        /* */
        Transform* m_transform;

        /* */
        Rotation* m_rotation;

        /* */
        Vector* m_position;

        /* */
        Vector* m_scale;

        /* */
        Material* m_material;

        /* */
        Color* m_color;
    };
}

#endif // SCENEOBJECT_H