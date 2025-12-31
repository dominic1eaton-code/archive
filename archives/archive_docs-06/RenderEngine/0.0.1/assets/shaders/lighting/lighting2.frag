#version 460
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec3 FragPosition;
layout(location = 1) in vec3 FragNormal;
layout(location = 2) in vec2 FragTexture;

// output
layout(location = 0) out vec4 FragColor;

// data
struct GPUMaterial
{
    vec3  ambient;
    vec3  diffuse;
    vec3  specular;
    float shine;
};

struct GPULight
{
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
    vec3 position;
};

// push constants
//push constants block
layout(push_constant) uniform FragData
{
    vec3 viewPosition;
    int  numLights;
} fragData;

// ubos
layout(binding = 0) readonly buffer Lights
{
	GPULight light[];
} lights;

layout(binding = 1) uniform GPUMesh
{
	GPUMaterial material;
} mesh;

// calculating basic lighting
vec3 calculateLighting(GPULight light, vec3 normal, vec3 viewDirection)
{
    // calculate ambient
    vec3 ambient = light.ambient * mesh.material.ambient;
  	
    // calculate diffuse 
    vec3 lightDirection = normalize(light.position - FragPosition);
    float diff = max(dot(normal, lightDirection), 0.0);
    vec3 diffuse = light.diffuse * (diff * mesh.material.diffuse);

    // calculate specular
    vec3 reflectDirection = reflect(-lightDirection, normal); 
    float spec = pow(max(dot(viewDirection, reflectDirection), 0.0), mesh.material.shine);
    vec3 specular = light.specular * spec * mesh.material.specular;

    // compute final lighting result
    return (ambient + diffuse + specular);
}

// called for every fragment
void main()
{
    // properties
    vec3 normal = normalize(FragNormal);
    vec3 viewDirection = normalize(fragData.viewPosition - FragPosition);
    vec3 result;
    float alpha = 1.0;

    // phase 1: calculate cummulative lighting
    for(int i = 0; i < fragData.numLights; i++)
        result += calculateLighting(lights.light[i], normal, viewDirection);

    // final fragment color
    FragColor = vec4(result, alpha);
}
