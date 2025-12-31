// @header
// @copyright
// @brief
// @note 
#version 460

//
layout(location = 0) in vec3 iPosition;
layout(location = 2) in vec4 iColor;
layout(location = 1) in vec3 iNormal;
layout(location = 3) in vec2 iTexture;

//
layout(location = 0) out vec3 oColor;
layout(location = 1) out vec2 oTexture;
layout(location = 1) out vec3 oNormal;

//
layout(binding = 0) uniform GPUCamera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

struct MeshData
{
    mat4 model;
};

layout(binding = 1) buffer GPUMesh
{
    MeshData models[];
} meshes;

//
void main()
{
    vec3 normal = normalize(iNormal);
    mat4 model = meshes.models[gl_BaseInstance].model;
    mat4 transform = camera.proj * camera.view * camera.model;

    gl_Position = transform * model * vec4(iPosition, 1.0);
    oColor = iColor;
    oTexture = iTexture;
    oNormal = normal;
}
