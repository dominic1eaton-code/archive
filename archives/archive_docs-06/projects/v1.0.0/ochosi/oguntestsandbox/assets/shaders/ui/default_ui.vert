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


vec3 s1[4] = vec3[](
    vec3(-0.5, -0.5, 0.0),
    vec3(0.5, -0.5, 0.0),
    vec3(0.5, 0.5, 0.0),
    vec3(-0.5, 0.5, 0.0)
);

vec3 s2[4] = vec3[](
    vec3(-1.0, -1.0, 0.0),
    vec3(1.0, -1.0, 0.0),
    vec3(1.0, 1.0, 0.0),
    vec3(-1.0, 1.0, 0.0)
);

vec3 s4[4] = vec3[](
    vec3( 0.05725154, -0.31190527, -.02294665),
    vec3(-0.19881446, -0.1640655, 0.186130360),
    vec3(-0.19881446,  0.23017389, -0.09263898),
    vec3( 0.05725154,  0.08233411, -0.301716)
);

// vec3 s3[4] = vec3[](
//     vec3( 1.0,  1.0,  0.0), // top right
//     vec3( 1.0, -1.0,  0.0), // top left 
//     vec3(-1.0, -1.0,  0.0), // bottom left 
//     vec3(-1.0,  1.0,  0.0)  // bottom right
// );

vec3 s3[4] = vec3[](
    vec3( 1.0,  1.0,  0.0), // bottom right
    vec3( 1.0, -1.0,  0.0), // top left 
    vec3(-1.0, -1.0,  0.0), // top left 
    vec3(-1.0,  1.0,  0.0)  // bottom right
);

vec4 color[4] = vec4[] (
    vec4(1.0, 0.0, 1.0, 1.0), // pink
    vec4(0.0, 1.0, 0.0, 1.0),
    vec4(1.0, 1.0, 1.0, 1.0),
    vec4(0.0, 0.0, 0.0, 1.0)
);

//
void main()
{
    // gl_PointSize = 1.0;
    mat4 model = meshes.models[gl_BaseInstance].model;
    mat4 transform = camera.proj * camera.view * camera.model;

    // out
    // gl_Position = transform * (vec4(iPosition, 1.0) + model);
    vec4 clip = transform * vec4(iPosition, 1.0);
    // gl_Position = vec4(clip.xy, 0.0, 1.0);
    // gl_Position =  vec4(iPosition, 1.0);

    float bound = 1.0f;
    
    // gl_Position = vec4(s4[gl_VertexIndex], 1.0);
    gl_Position = vec4(s3[gl_VertexIndex], bound);
    // gl_Position =  transform * vec4(s3[gl_VertexIndex], 1.0);
    // oColor = iColor;
    oColor = color[gl_VertexIndex];
    oTexture = iTexture;
    oNormal = iNormal;
    oPosition = iPosition;
}
