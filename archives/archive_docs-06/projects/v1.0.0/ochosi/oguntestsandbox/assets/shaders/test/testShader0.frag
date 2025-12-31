// @header
// @copyright
// @brief
// @note 
#version 450

//
layout(location = 0) in vec4 iColor;
layout(location = 1) in vec2 iTexture;
layout(location = 2) in vec3 iNormal;
layout(location = 3) in vec3 iPosition;
// flat layout(location = 4) in int iInstance;

//
layout(location = 0) out vec4 oColor;

//
layout(binding = 2) uniform sampler2D texsampler;

layout(binding = 3) uniform GPUView
{
    vec4 position;
} view;

struct DirLight
{
    vec4 direction;
    vec4 ambient;
    vec4 diffuse;
    vec4 specular;
};

struct PointLight 
{
    vec4 position;
    vec4 ambient;
    vec4 diffuse;
    vec4 specular;
    float k0;
    float k1;
    float k2;
};


layout(binding = 4) uniform sampler2D texdiffuse[];

// layout(std140, binding = 4) buffer DirectionalLight
// {
//     DirLight light[];
// } dirLight;

// layout(binding = 5) uniform GPUMaterial
// {
//     float shininess;
// } material;

// layout(binding = 7) uniform sampler2D texdiffuse;
// layout(binding = 8) uniform sampler2D texspecular;

// #define NR_POINT_LIGHTS 1

vec4 CalcDirLight(DirLight light, float shine, vec3 normal, vec3 viewDir);
vec4 CalcPointLight(PointLight light, vec3 normal, vec3 fragPos, vec3 viewDir, float shine);

void main()
{
    vec3 norm = normalize(iNormal);
    vec3 viewDir = normalize(vec3(view.position.x, view.position.y, view.position.z) - iPosition);
    vec4 result = vec4(0.0, 0.0, 0.0, 1.0);

    // compute lighting
    DirLight light0;
    light0.ambient = vec4(0.8, 0.8, 0.0, 1.0);
    light0.diffuse = vec4(1.0, 1.0, 1.0, 1.0);
    light0.specular = vec4(1.0, 1.0, 1.0, 1.0);
    light0.direction = vec4(-0.5f, -0.8f, -0.1f, 1.0);
    float shine = 0.8;
    result += CalcDirLight(light0, shine, norm, viewDir);
    // vec4 result = CalcDirLight(dirLight.light[iInstance], norm, viewDir);
    
    PointLight plight0;
    plight0.position = vec4(0.5, 0.5, 0.0, 1.0f);
    plight0.ambient = vec4(0.4f, 0.0f, 0.0f, 1.0f);
    plight0.diffuse = vec4(0.8f, 0.0f, 0.0f, 1.0f);
    plight0.specular = vec4(0.5f, 0.5f, 0.5f, 1.0f);
    plight0.k0 = 1.0f;
    plight0.k1 = 0.12f;
    plight0.k2 = 0.032f;
    result += CalcPointLight(plight0, norm, iPosition, viewDir, shine);

    PointLight p1;
    p1.position = vec4(1.5, 0.5, 0.5, 1.0f);
    p1.ambient = vec4(0.8f, 0.8f, 0.8f, 1.0f);
    p1.diffuse = vec4(0.8f, 0.8f, 0.8f, 1.0f);
    p1.specular = vec4(0.8f, 0.8f, 0.8f, 1.0f);
    p1.k0 = 1.0f;
    p1.k1 = 0.4f;
    p1.k2 = 0.09f;
    result += CalcPointLight(p1, norm, iPosition, viewDir, shine);

    // oColor = iColor;
    // vec2 coord = gl_PointCoord - vec2(0.5);
    // outColor = vec4(fragColor, 0.5 - length(coord));
    oColor = result * texture(texsampler, iTexture);
    // oColor = texture(texsampler, iTexture);
}

// calculates the color when using a directional light.
vec4 CalcDirLight(DirLight light, float shine, vec3 normal, vec3 viewDir)
{
    // vec3 lightDir = normalize(-vec3(light.direction.x, light.direction.y, light.direction.z));
    vec3 lightDir = normalize(-light.direction.xyz);
    // diffuse shading
    float diff = max(dot(normal, lightDir), 0.0);
    // specular shading
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = pow(max(dot(viewDir, reflectDir), 0.0), shine);
    // combine results
    vec4 ambient = light.ambient * texture(texsampler, iTexture);
    vec4 diffuse = light.diffuse * diff * texture(texsampler, iTexture);
    vec4 specular = light.specular * spec * texture(texsampler, iTexture);
    return (ambient + diffuse + specular);
}

vec4 CalcPointLight(PointLight light, vec3 normal, vec3 fragPos, vec3 viewDir, float shine)
{
    vec3 lightDir = normalize(light.position.xyz - fragPos);
    // diffuse shading
    float diff = max(dot(normal, lightDir), 0.0);
    // specular shading
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = pow(max(dot(viewDir, reflectDir), 0.0), shine);
    // attenuation
    float distance = length(light.position.xyz - fragPos);
    float attenuation = 1.0 / (light.k0 + light.k1 * distance + light.k2 * (distance * distance));    
    // combine results
    vec4 ambient = light.ambient * texture(texsampler, iTexture);
    vec4 diffuse = light.diffuse * diff * texture(texsampler, iTexture);
    vec4 specular = light.specular * spec * texture(texsampler, iTexture);
    ambient *= attenuation;
    diffuse *= attenuation;
    specular *= attenuation;
    return (ambient + diffuse + specular);
}