// @header
// @copyright
// @brief
// @note 
#version 450

//
layout(location = 0) in vec4 iPosition;
layout(location = 2) in vec4 iNormal;
layout(location = 3) in vec4 iTexture;

//
layout(location = 0) out vec4 oColor;

//
layout(binding = 1) uniform sampler2D stexture;
uniform vec3 viewPosition;

struct GPUMaterial
{
    sampler2D diffuse;
    sampler2D specular;
    float shininess;
}; 

layout(binding = 0) uniform GPULights
{
    int numPoints;
    mat4 numDirectionals;
    mat4 numSpots;
} lights;

struct PointLight
{
    vec3 position;
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
    float k0;
    float k1;
    float k2;
};

struct SpotLight
{
    vec3 position;
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
    float k0;
    float k1;
    float k2;
    float c0;
    float c1;
};

struct DirectionLight
{
    vec3 dkrection;
    vec3 ambient;
    vec3 diffuse;
    vec3 specular;
};

#define MAX_POINT_LIGHTS 10
#define MAX_SPOT_LIGHTS 10
#define MAX_DIRECTION_LIGHTS 10

// uniform PointLight pointLights[lights.numPoints];
// uniform SpotLight spotLights[lights.numSpots];
// uniform DirectionLight directionLights[lights.numDirectionals];
uniform GPUMaterial material;
layout(std430, binding = 0) buffer GPUPointLights
{
    PointLight light[];
} pointLights;

vec3 computeDirectionLight(DirectionLight light, vec3 normal, vec3 viewDirection);
vec3 computePointLight(PointLight light, vec3 normal, vec3 viewDirection);
vec3 computeSpotLight(SpotLight light, vec3 normal, vec3 viewDirection);

//
void main()
{
    vec3 result = vec3(0.0f, 0.0f, 0.0f);
    vec3 normal = normalize(iNormal);
    vec3 viewDirection = normalize(viewPosition - iPosition);

    for (int i = 0; i < lights.numPoints; i++)
    {    
        result += computeDirectionLight(directionLights[i], normal, viewDirection);
    }

    for (int i = 0; i < lights.numDirectionals; i++)
    {   
        result += computePointLight(pointLights[i], normal, viewDirection);
    }
    
    for (int i = 0; i < lights.numSpots; i++)
    {
        result += computeSpotLight(spotLights[i], normal, viewDirection);
    }
 
    oColor = vec4(result, 1.0) * texture(stexture, iTexture);
}

void computeDirectionLight(DirectionLight light, vec3 normal, vec3 viewDirection)
{
    vec3 lightDir = normalize(-light.direction);
    // diffuse shading
    float diff = max(dot(normal, lightDir), 0.0);
    // specular shading
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = pow(max(dot(viewDirection, reflectDir), 0.0), material.shininess);
    // combine results
    vec3 ambient = light.ambient* vec3(texture(material.diffuse, iTexture));
    vec3 diffuse = light.diffuse * diff * vec3(texture(material.diffuse, iTexture));
    vec3 specular = light.specular * spec * vec3(texture(material.specular, iTexture));
    return (ambient + diffuse + specular);
}

void computePointLight(PointLight light, vec3 normal, vec3 viewDirection)
{
    vec3 lightDir = normalize(light.position - fragPos);
    // diffuse shading
    float diff = max(dot(normal, lightDir), 0.0);
    // specular shading
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = pow(max(dot(viewDirection, reflectDir), 0.0), material.shininess);
    // attenuation
    float distance = length(light.position - fragPos);
    float attenuation = 1.0 / (light.constant + light.linear * distance + light.quadratic * (distance * distance));    
    // combine results
    vec3 ambient = light.ambient * vec3(texture(material.diffuse, iTexture));
    vec3 diffuse = light.diffuse * diff * vec3(texture(material.diffuse, iTexture));
    vec3 specular = light.specular * spec * vec3(texture(material.specular, iTexture));
    ambient *= attenuation;
    diffuse *= attenuation;
    specular *= attenuation;
    return (ambient + diffuse + specular);
}

void computeSpotLight(SpotLight light, vec3 normal, vec3 viewDirection)
{
    vec3 lightDir = normalize(light.position - fragPos);
    // diffuse shading
    float diff = max(dot(normal, lightDir), 0.0);
    // specular shading
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = pow(max(dot(viewDirection, reflectDir), 0.0), material.shininess);
    // attenuation
    float distance = length(light.position - fragPos);
    float attenuation = 1.0 / (light.constant + light.linear * distance + light.quadratic * (distance * distance));    
    // spotlight intensity
    float theta = dot(lightDir, normalize(-light.direction)); 
    float epsilon = light.cutOff - light.outerCutOff;
    float intensity = clamp((theta - light.outerCutOff) / epsilon, 0.0, 1.0);
    // combine results
    vec3 ambient = light.ambient * vec3(texture(material.diffuse, iTexture));
    vec3 diffuse = light.diffuse * diff * vec3(texture(material.diffuse, iTexture));
    vec3 specular = light.specular * spec * vec3(texture(material.specular, iTexture));
    ambient *= attenuation * intensity;
    diffuse *= attenuation * intensity;
    specular *= attenuation * intensity;
    return (ambient + diffuse + specular);
}
