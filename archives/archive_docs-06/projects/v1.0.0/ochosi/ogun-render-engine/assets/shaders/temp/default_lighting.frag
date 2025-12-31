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

struct GPULightData
{
    vec4 direction; // w = inner cutoff
    vec4 position; // w = outer cutoff
    vec4 ambient;
    vec4 diffuse;
    vec4 specular;
    vec4 parameters;
    vec4 options; // x = relative_direction; y = attenuation; z = intensity; w = materialID
};

layout(std140, binding = 1) buffer GPULight
{
    GPULightData data[];
} lights;

layout(binding = 2) uniform GPUScene
{
    vec4 view;
    vec4 parameters;
} scene;

#define MAX_TEXTURES 10
layout(binding = 3) uniform sampler2D materials[MAX_TEXTURES];

vec4 compute_lighting(GPULightData light, vec3 normal, vec3 viewdir);

void main()
{
    vec3 norm = normalize(inormal);
    vec3 view_direction = normalize(vec3(scene.view.x, scene.view.y, scene.view.z) - iposition);
    vec4 result = vec4(0.0, 0.0, 0.0, 1.0);

    // select materials
    vec4 material;
    // int textureID = int(itexture.z);
    int textureID = int(1);
    if (textureID == -1) { material = icolor; }
    else { material = texture(materials[textureID], itexture.xy); }
    // if (textureID >= 0) { material = texture(materials[textureID], itexture.xy); }
    // else { material = icolor; }
    for (int l = 0; l < scene.parameters.x; l++)
    {
        result += compute_lighting(lights.data[l], norm, view_direction) * material;
    }
    ocolor = result;
    // ocolor = icolor;
    // ocolor = material;
}

vec4 compute_lighting(GPULightData light, vec3 normal, vec3 viewdir)
{
    vec3 lightdir;
    float attenuation;
    float intensity;

    if (light.options.x == 1.0f)
    {
        vec3 lightdir = normalize(light.position.xyz - iposition);
    }
    else
    {
        vec3 lightdir = normalize(-light.direction.xyz);
    }

    if (light.options.y == 1.0f)
    {
        float distance = length(light.position.xyz - iposition);
        attenuation = 1.0 / (light.parameters.x + light.parameters.y * distance + light.parameters.z * (distance * distance)); 
    }
    else
    {
        attenuation = 1.0F;
    }

    if (light.options.z == 1.0f)
    {
        float theta = dot(lightdir, normalize(-light.direction.xyz)); 
        float epsilon = light.direction.w - light.position.w;
        intensity = clamp((theta - light.position.w) / epsilon, 0.0, 1.0);
    }
    else
    {
        intensity = 1.0F;
    }

    float diff = max(dot(normal, lightdir), 0.0);
    vec3 reflectdir = reflect(-lightdir, normal);
    float spec = max(dot(viewdir, reflectdir), 0.0);
    vec4 ambient = light.ambient;
    vec4 diffuse = light.diffuse * diff;
    vec4 specular = light.specular * spec;
    ambient *= attenuation * intensity;
    diffuse *= attenuation * intensity;
    specular *= attenuation * intensity;
    return (ambient + diffuse + specular);
}