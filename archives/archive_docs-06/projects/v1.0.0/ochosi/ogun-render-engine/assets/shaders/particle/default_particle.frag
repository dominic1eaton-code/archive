// @copyright
// @brief
#version 460

layout(location = 0) in vec3 icolor;
layout(location = 0) out vec4 ocolor;

void main() 
{
    vec2 coord = gl_PointCoord - vec2(0.5);
    ocolor = vec4(icolor, 0.5 - length(coord));
}
