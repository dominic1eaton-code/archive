#version 460
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec3 FragPosition;
layout(location = 1) in vec3 Normal;

// output
layout(location = 0) out vec4 fragColor;

// objects
// layout(binding = 1) uniform Light
// {
//     vec3 position;
//     vec3 color;
//     float ambient;
// } light;
//
// layout(binding = 2) uniform Mesh
// {
//     vec3 color;
// } mesh;

struct LightData
{
    vec3 position;
    vec3 color;
    float ambient;
};

struct MeshData
{
    vec3 color;
};

layout(binding = 1) readonly buffer Meshes
{
	MeshData data[];
} meshes;

layout(binding = 2) readonly buffer Lights
{
	LightData data[];
} lights;

layout(push_constant) uniform RenderObjectIndices
{
	int light;
	int mesh;
} indices;

// called for every fragment
void main()
{
    // calculate ambient
    vec3 ambient = lights.data[indices.light].ambient * lights.data[indices.light].color;
  	
    // calculate diffuse 
    vec3 norm = normalize(Normal);
    vec3 lightDir = normalize(lights.data[indices.light].position - FragPosition);
    float diff = max(dot(norm, lightDir), 0.0);
    vec3 diffuse = diff * lights.data[indices.light].color;

    // compute final lighting result
    vec3 result = (ambient + diffuse) * meshes.data[indices.mesh].color;

    // final fragment color
    fragColor = vec4(result, 1.0);
}
