#version 450
#extension GL_EXT_scalar_block_layout : enable

layout(std140, binding = 0) uniform ubo140 {
    vec3 a;
    vec2 b;
    vec2 c;
    vec3 d;
} x;

layout(std430, binding = 1) uniform ubo430 {
    vec3 a;
    vec2 b;
    vec2 c;
    vec3 d;
} y;

layout(scalar, binding = 0) uniform uboScalar {
    vec3 a;
    vec2 b;
    vec2 c;
    vec3 d;
} z;

void main() {}