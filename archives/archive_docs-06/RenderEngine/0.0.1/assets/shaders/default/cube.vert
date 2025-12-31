#version 450
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec3 inPosition;
layout(location = 1) in vec3 inColor;

// output
layout(location = 0) out vec3 fragColor;

// bjects
layout(binding = 0) uniform Camera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

// invoked for every vertex
void main()
{
    // built-in gl_VertexIndex variable contains the index of the current vertex.
    gl_Position = camera.proj * camera.view * camera.model * vec4(inPosition, 1.0);
    fragColor = inColor;
}
