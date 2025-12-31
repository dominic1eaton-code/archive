// @copyright
// @brief
#version 460

layout(location = 0) in vec4 icolor;
layout(location = 1) in vec3 iposition;
layout(location = 2) in vec3 inormal;
layout(location = 3) in vec3 itangent;
layout(location = 4) in vec3 ibitangent;
layout(location = 5) in vec3 itexture; // xy = texture_coordinates; z = textureID

layout(location = 0) out vec4 ocolor;
layout(location = 1) out vec3 oposition;
layout(location = 2) out vec3 onormal;
layout(location = 3) out vec3 otangent;
layout(location = 4) out vec3 obitangent;
layout(location = 5) out vec3 otexture; // xy = texture_coordinates; z = textureID

layout(binding = 0) uniform GPUCamera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

void main()
{
    mat4 transform = camera.proj * camera.view * camera.model;
    gl_Position = transform * vec4(iposition, 1.0);
    ocolor = icolor;
    oposition = iposition;
    onormal = inormal;
    otangent = itangent;
    obitangent = obitangent;
    otexture = itexture;
}