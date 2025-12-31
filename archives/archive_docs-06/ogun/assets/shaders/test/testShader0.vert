// @header
// @copyright
// @brief
// @note 
#version 460

//
layout(location = 0) in vec3 iPosition;
layout(location = 1) in vec4 iColor;
layout(location = 2) in vec2 iTexture;
// layout(location = 2) in vec3 iNormal;

//
layout(location = 0) out vec4 oColor;
layout(location = 1) out vec2 oTexture;
// layout(location = 2) out vec3 oNormal;

// //
layout(binding = 0) uniform GPUCamera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

struct GPUMeshData
{
    // mat4 model;
    vec3 position;
};

layout(std140, binding = 1) buffer GPUMesh
{
    GPUMeshData models[];
} meshes;


// vec3 positions[4] = vec3[](
//     vec3(-0.5, -0.5, 0.0),
//     vec3(0.5, -0.5, 0.0),
//     vec3(0.5, 0.5, 0.0),
//     vec3(-0.5, 0.5, 0.0)
// );

// vec4 colors[4] = vec4[](
//     vec4(1.0, 0.0, 0.0, 1.0),
//     vec4(0.0, 1.0, 0.0, 1.0),
//     vec4(0.0, 0.0, 1.0, 1.0),
//     vec4(1.0, 0.0, 1.0, 1.0)
// );

vec3 positions[3] = vec3[](
    vec3(0.5, -0.5, 0.0),
    vec3(0.5, 0.5, 0.0),
    vec3(-0.5, 0.5, 0.0)
);

vec4 colors[3] = vec4[](
    vec4(1.0, 0.0, 0.0, 1.0),
    vec4(0.0, 1.0, 0.0, 1.0),
    vec4(0.0, 0.0, 1.0, 1.0)
);

//
void main()
{
    // gl_Position = vec4(positions[gl_VertexIndex], 1.0);
    // oColor = colors[gl_VertexIndex];

    // vec3 normal = normalize(iNormal);
    // mat4 model = meshes.models[gl_BaseInstance].model;
    vec3 model = meshes.models[gl_BaseInstance].position;
    mat4 transform = camera.proj * camera.view * camera.model;

    // gl_Position = transform * model * vec4(iPosition, 1.0);
    // gl_Position = transform * vec4(iPosition, 1.0);
    // gl_Position = vec4(iPosition, 1.0);
    gl_Position = transform * (vec4(iPosition, 1.0) + vec4(model, 1.0));
    oColor = iColor;
    oTexture = iTexture;
    // oNormal = normal;

}
