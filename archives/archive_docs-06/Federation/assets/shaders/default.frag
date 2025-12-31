#version 450
// input
layout (location = 0) in vec3 vColor;
layout (location = 1) in vec2 vNormal;
layout (location = 2) in vec2 vTexCoord;

// output
layout (location = 0) out vec3 oColor;

// model material
struct Material
{
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
    float shininess;
};

layout(std140, set = 1, binding = 0) readonly buffer MaterialBuffer
{
    Material materials[];
} materialBuffer;


// light casters
struct Light
{
    vec3 position;
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
};

layout(std140, set = 1, binding = 0) readonly buffer LightBuffer
{
    Light lights[];
} lightBuffer;


void main()
{
    // compute lighting
    // ambient
    vec3 ambient = lightBuffer.lights[gl_BaseInstance].ambient * materialBuffer.materials[gl_BaseInstance].ambient;
       
    // diffuse 
    vec3 normal = normalize(vNormal);
    vec3 lightDirection = normalize(lightBuffer.lights[gl_BaseInstance].position - vColor);
    float diff = max(dot(normal, direction), 0.0);
    vec3 diffuse = lightBuffer.lights[gl_BaseInstance].diffuse * (diff * materialBuffer.materials[gl_BaseInstance].diffuse);
    
    // specular
    vec3 viewDirection = normalize(viewPos - vColor);
    vec3 reflectDirection = reflect(-lightDirection, normal);  
    float spec = pow(max(dot(viewDirection, reflectDirection), 0.0), materialBuffer.materials[gl_BaseInstance].shininess);
    vec3 specular = lightBuffer.lights[gl_BaseInstance].specular * (spec * materialBuffer.materials[gl_BaseInstance].specular);  
    
    // output calculated light color
    vec3 result = ambient + diffuse + specular;
    oColor = vec4(result, 1.0);
} 