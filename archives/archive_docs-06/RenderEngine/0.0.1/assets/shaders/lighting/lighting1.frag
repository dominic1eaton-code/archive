#version 460
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec3 FragPosition;
layout(location = 1) in vec3 FragNormal;
layout(location = 2) flat in int FragIndex;

// output
layout(location = 0) out vec4 FragColor;

// data
struct MaterialData
{
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
    float shininess;
};

struct LightData
{
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
    vec3 position;
};

// ubos
layout(binding = 0) uniform Camera
{
    mat4 model;
    mat4 view;
    mat4 proj;
    vec3 position;
} camera;

layout(binding = 1) readonly buffer Lights
{
	LightData data[];
} lights;

layout(binding = 2) readonly buffer Meshes
{
	MaterialData material[];
} meshes;

// called for every fragment
void main()
{
    // calculate ambient
    vec3 ambient = lights.data[FragIndex].ambient * meshes.material[FragIndex].ambient;
  	
    // calculate diffuse 
    vec3 norm = normalize(FragNormal);
    vec3 lightDir = normalize(lights.data[FragIndex].position - FragPosition);
    float diff = max(dot(norm, lightDir), 0.0);
    vec3 diffuse = lights.data[FragIndex].diffuse * (diff * meshes.material[FragIndex].diffuse);

    // calculate specular
    vec3 viewDir = normalize(camera.position - FragPosition);
    vec3 reflectDir = reflect(-lightDir, norm);  
    float spec = pow(max(dot(viewDir, reflectDir), 0.0), meshes.material[FragIndex].shininess);
    vec3 specular = lights.data[FragIndex].specular * spec * meshes.material[FragIndex].specular;

    // compute final lighting result
    vec3 result = (ambient + diffuse + specular);

    // final fragment color
    FragColor = vec4(result, 1.0);
}
