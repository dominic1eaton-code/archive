#version 450

// input
layout (location = 0) in vec3 vPosition;
layout (location = 1) in vec3 vNormal;
layout (location = 2) in vec3 vColor;
layout (location = 3) in vec2 vTexCoord;

// output
layout (location = 0) out vec3 oColor;
layout (location = 1) out vec3 oNormal;
layout (location = 2) out vec2 oTexCoord;

// camera
layout(set = 0, binding = 0) uniform CameraBuffer
{
    mat4 view;
    mat4 projection;
    mat4 viewproj; 
} cameraBuffer;

// model
struct Model
{
	mat4 transform;
}; 

layout(std140,set = 1, binding = 0) readonly buffer ModelBuffer
{
    Model models[];
} modelBuffer;


void main()
{
    // transformation matrices
    mat4 modelTransform = modelBuffer.models[gl_BaseInstance].transform;
    mat4 cameraTransform = (cameraBuffer.viewproj * modelTransform);
    mat3 normalTransform = transpose(inverse(mat3(modelTransform)));

    // output
    gl_Position = cameraTransform * vec4(vPosition, 1.0f);
    oNormal = normalTransform;
    oColor = vColor;
    oTexCoord = vTexCoord;
}