// @header
// @copyright
// @brief
// @note 
#version 460

// vertex position
layout (location = 0) in vec3 iposition;
layout (location = 1) in vec4 icolor;
layout (location = 2) in vec2 itexture;
layout (location = 0) out vec2 otexture;

void main()
{
    gl_Position = vec4(iposition, 1.0);
    otexture = itexture;
}