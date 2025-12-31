#version 460
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec3 vPosition;
layout(location = 1) in vec3 vNormal;
layout(location = 2) in vec2 vTexture;

// output
layout(location = 0) out vec3 FragPosition;
layout(location = 1) out vec3 FragNormal;
layout(location = 2) out vec2 FragTexture;

// objects
layout(binding = 0) uniform GPUCamera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

// invoked for every vertex
void main()
{
    FragPosition = vec3(camera.model  * vec4(vPosition, 1.0));         // fragment vertex position
    FragNormal = vNormal;                                              // fragment vertex normal
    FragTexture = vTexture;                                            // fragment vertex normal
    gl_Position = camera.proj * camera.view * vec4(FragPosition, 1.0); // built-in gl_VertexIndex variable contains the index of the current vertex.
}
