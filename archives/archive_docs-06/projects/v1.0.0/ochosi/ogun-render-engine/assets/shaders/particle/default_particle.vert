// @copyright
// @brief
#version 460

layout(location = 0) in vec2 iposition;
layout(location = 1) in vec4 icolor;
layout(location = 0) out vec3 ocolor;

// test values
vec2 s2[4] = vec2[]
(
    vec2(1.0, 1.0),
    vec2(0.0, 1.0),
    vec2(-1.0, 0.0),
    vec2(0.0, -1.0)
);

void main()
{
    gl_PointSize = 14.0;
    gl_Position = vec4(iposition.xy, 0.0, 1.0);
    // gl_Position = vec4(s2[gl_VertexIndex], 0.0, 1.0);
    ocolor = icolor.rgb;
}
