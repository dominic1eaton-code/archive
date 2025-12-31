#version 450
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec2 inPosition;
layout(location = 1) in vec3 inColor;

// output
layout(location = 0) out vec3 fragColor;

// invoked for every vertex
void main()
{
    //  built-in gl_VertexIndex variable contains the index of the current vertex.
    gl_Position = vec4(inPosition, 0.0, 1.0);
    fragColor = inColor;
}
