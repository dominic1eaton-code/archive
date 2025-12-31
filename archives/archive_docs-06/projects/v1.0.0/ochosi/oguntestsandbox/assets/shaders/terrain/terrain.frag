// @header
// @copyright
// @brief
// @note 
#version 450
// #version 410 core

// in float Height;
// out vec4 ocolor;

layout(location = 0) in float Height;

//
layout(location = 0) out vec4 ocolor;


void main()
{
    float max_tesselation_level = 64.0f;
    float tesselation_offset = 16;
    float h = (Height + tesselation_offset) / max_tesselation_level;
    ocolor = vec4(h, h, h, 1.0);
}