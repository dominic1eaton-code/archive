// @header
// @copyright
// @brief
// @note 
#version 450
// #version 410 core

// vertex position
layout (location = 0) in vec3 iposition;
layout (location = 1) in vec4 icolor;
layout (location = 2) in vec2 itexture;

// out vec2 otexture;
layout(location = 0) out vec2 otexture;

void main()
{
    // convert XYZ vertex to XYZW homogeneous coordinate
    gl_Position = vec4(iposition, 1.0);

    // pass texture coordinate though
    otexture = itexture;
}