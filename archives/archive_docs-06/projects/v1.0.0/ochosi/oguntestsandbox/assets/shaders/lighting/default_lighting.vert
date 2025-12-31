// @header
// @copyright
// @brief
// @note 
#version 460

//
layout(location = 0) in vec3 iPosition;
layout(location = 1) in vec4 iColor;
layout(location = 2) in vec2 iTexture;
layout(location = 3) in vec3 iNormal;

//
layout(location = 0) out vec4 oColor;
layout(location = 1) out vec2 oTexture;
layout(location = 2) out vec3 oNormal;
layout(location = 3) out vec3 oPosition;
// layout(location = 4) out int oInstance;

//
layout(binding = 0) uniform GPUCamera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

struct GPUMeshData
{
    mat4 model;
};

layout(std140, binding = 1) buffer GPUMesh
{
    GPUMeshData models[];
} meshes;


vec3 positions[4] = vec3[](
    vec3(-0.5, -0.5, 0.0),
    vec3(0.5, -0.5, 0.0),
    vec3(0.5, 0.5, 0.0),
    vec3(-0.5, 0.5, 0.0)
);

vec3 s2[4] = vec3[](
    vec3(-1.0, -1.0, 0.0),
    vec3(0.5, -0.5, 0.0),
    vec3(0.5, 0.5, 0.0),
    vec3(-0.5, 0.5, 0.0)
);

//
void main()
{
    // gl_PointSize = 1.0;
    mat4 model = meshes.models[gl_BaseInstance].model;
    mat4 transform = camera.proj * camera.view * camera.model;

    // out
    // gl_Position = transform * (vec4(iPosition, 1.0) + model);
    gl_Position = transform * vec4(iPosition, 1.0);
    // gl_Position =  vec4(iPosition, 1.0);
    
    // gl_Position =  transform * vec4(s2[gl_VertexIndex], 1.0);
    oColor = iColor;
    oTexture = iTexture;
    oNormal = iNormal;
    oPosition = iPosition;
}
