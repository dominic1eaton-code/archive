/**
 * @copyright
 * @brief
 * @note
 */
#pragma once
#ifndef sema_noise_h
#define sema_noise_h

namespace sema
{

struct SVector2D
{
    float x;
    float y;
};

struct SVector3D
{
    float x;
    float y;
    float z;
};

struct SVector4D
{
    float x;
    float y;
    float z;
    float w;
};

struct SVectorND
{

};

struct SQuaternion
{
    float x;
    float y;
    float z;
    float w;
};

struct STensor
{

};

struct SRotation
{
    SRotation(float yaw, float pitch, float roll)
        : yaw(yaw), pitch(pitch), roll(roll)
    {};

    float yaw;
    float pitch;
    float roll;
};

struct STranslation
{
    STranslation(float x, float y, float z)
        : x(x), y(y), z(z)
    {};

    float x;
    float y;
    float z;
};

struct SScale
{
    SScale(float x, float y, float z)
        : x(x), y(y), z(z)
    {}

    float x;
    float y;
    float z;
};

struct SSize
{
    SSize(float x, float y, float z)
        : x(x), y(y), z(z)
    {};

    float x;
    float y;
    float z;
};

struct STransform
{
    STransform(SRotation rotation, STranslation translation, SScale scale, SSize size)
        : rotation(rotation), translation(translation), scale(scale), size(size)
    {}

    SRotation rotation;
    STranslation translation;
    SScale scale;
    SSize size;
};

struct SColorRGBA
{
    SColorRGBA(float r, float g, float b, float a)
        : r(r), g(g), b(b), a(a)
    {};

    float r;
    float g;
    float b;
    float a;
};

} // namespace sema


#endif // sema_noise_h