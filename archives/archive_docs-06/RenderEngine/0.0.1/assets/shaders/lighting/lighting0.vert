#version 460
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec3 aPosition;
layout(location = 1) in vec3 aColor;
layout(location = 2) in vec3 aNormal;

// output
layout(location = 0) out vec3 FragPosition;
layout(location = 0) out vec3 FragColor;
layout(location = 1) out vec3 FragNormal;

// objects
layout(binding = 0) uniform Camera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

// invoked for every vertex
void main()
{
    FragPosition = vec3(camera.model  * vec4(aPosition, 1.0));         // fragment vertex position
    FragColor = aColor;                                                // fragment vertex color
    FragNormal = aNormal;                                              // fragment vertex normal
    gl_Position = camera.proj * camera.view * vec4(FragPosition, 1.0); // built-in gl_VertexIndex variable contains the index of the current vertex.
}
