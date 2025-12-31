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

vec3 s2[4] = vec3[](
    vec3(-1.0, -1.0, 0.0),
    vec3(0.5, -0.5, 0.0),
    vec3(0.5, 0.5, 0.0),
    vec3(-0.5, 0.5, 0.0)
);

// struct GPUMeshData
// {
//     mat4 model;
// };
// layout(binding = 1) buffer GPUMesh
// {
//     GPUMeshData data[];
// } meshes;
// layout(push_constant) uniform GPUMeshInfo
// {
//     int meshID;
// } mesh_info;

void main()
{
    mat4 transform = camera.proj * camera.view * camera.model; // * meshes.data[mesh_info.meshID].model;
    // gl_Position =  transform * vec4(s2[gl_VertexIndex], 1.0);
    gl_Position = transform * vec4(iposition, 1.0);
    ocolor = icolor;
    oposition = iposition;
    onormal = inormal;
    otangent = itangent;
    obitangent = obitangent;
    otexture = itexture;
}