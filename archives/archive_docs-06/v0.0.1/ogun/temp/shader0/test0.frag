// @header
// @copyright
// @brief
// @note 
#version 450

//
layout(location = 0) in vec3 iPosition;
layout(location = 1) in vec3 iNormal;
layout(location = 2) in vec2 iTexture;

//
layout(location = 0) out vec4 oColor;

//
layout(binding = 1) uniform sampler2D stexture;
// uniform vec3 viewPosition;

// struct GPUMaterial
// {
//     sampler2D diffuse;
//     sampler2D specular;
//     float shininess;
// }; 

// layout(binding = 0) uniform GPULights
// {
//     int numPoints;
//     int numDirectionals;
//     int numSpots;
// } lights;


// struct DirectionLight
// {
//     float dirX;
//     float dirY;
//     float dirZ;
//     vec4 ambient;
//     vec4 diffuse;
//     vec4 specular;
// };

// struct PointLight
// {
//     float posX;
//     float posY;
//     float posZ;
//     vec4 ambient;
//     vec4 diffuse;
//     vec4 specular;
//     float k0;
//     float k1;
//     float k2;
// };

// struct SpotLight
// {
//     float dirX;
//     float dirY;
//     float dirZ;
//     float posX;
//     float posY;
//     float posZ;
//     vec4 ambient;
//     vec4 diffuse;
//     vec4 specular;
//     float k0;
//     float k1;
//     float k2;
//     float c0;
//     float c1;
// };

// uniform GPUMaterial material;

// layout(std430, binding = 0) buffer GPUPointLights
// {
//     PointLight lights[];
// } pointLights;

// layout(std430, binding = 0) buffer GPUDirectionLights
// {
//     DirectionLight lights[];
// } directionLights;

// layout(std430, binding = 0) buffer GPUSpotLights
// {
//     SpotLight lights[];
// } spotLigths;

// vec4 computeDirectionLight(DirectionLight light, vec3 normal, vec3 viewDirection)
// {
//     vec3 lightDir = normalize(-vec3(light.dirX, light.dirY, light.dirZ));
    
//     // diffuse shading
//     float diff = max(dot(normal, lightDir), 0.0);
    
//     // specular shading
//     vec3 reflectDir = reflect(-lightDir, normal);
//     float spec = pow(max(dot(viewDirection, reflectDir), 0.0), material.shininess);
    
//     // combine results
//     vec4 ambient = light.ambient * texture(material.diffuse, iTexture);
//     vec4 diffuse = light.diffuse * diff * texture(material.diffuse, iTexture);
//     vec4 specular = light.specular * spec * texture(material.specular, iTexture);
//     return (ambient + diffuse + specular);
// }

// vec4 computePointLight(PointLight light, vec3 normal, vec3 viewDirection, vec3 position)
// {
//     lPosition = vec3(light.posX, light.posY, light.posZ);
//     vec3 lightDir = normalize(lPosition - position);

//     // diffuse shading
//     float diff = max(dot(normal, lightDir), 0.0);

//     // specular shading
//     vec3 reflectDir = reflect(-lightDir, normal);
//     float spec = pow(max(dot(viewDirection, reflectDir), 0.0), material.shininess);
    
//     // attenuation
//     float distance = length(lPosition - position);
//     float attenuation = 1.0 / (light.k0 + light.k1 * distance + light.k2 * (distance * distance));    
    
//     // combine results
//     vec3 ambient = light.ambient * texture(material.diffuse, iTexture);
//     vec3 diffuse = light.diffuse * diff * texture(material.diffuse, iTexture);
//     vec3 specular = light.specular * spec * texture(material.specular, iTexture);
//     ambient *= attenuation;
//     diffuse *= attenuation;
//     specular *= attenuation;
//     return (ambient + diffuse + specular);
// }

// vec4 computeSpotLight(SpotLight light, vec3 normal, vec3 viewDirection, vec3 position)
// {
//     lPosition = vec3(light.posX, light.posY, light.posZ);
//     vec3 lightDir = normalize(lPosition - position);

//     // diffuse shading
//     float diff = max(dot(normal, lightDir), 0.0);

//     // specular shading
//     vec3 reflectDir = reflect(-lightDir, normal);
//     float spec = pow(max(dot(viewDirection, reflectDir), 0.0), material.shininess);
    
//     // attenuation
//     float distance = length(lPosition - position);
//     float attenuation = 1.0 / (light.k0 + light.k1 * distance + light.k2 * (distance * distance));    
    
//     // spotlight intensity
//     float theta = dot(lightDir, normalize(-vec3(light.dirX, light.dirY, light.dirZ))); 
//     float epsilon = light.c0 - light.c1;
//     float intensity = clamp((theta - light.c1) / epsilon, 0.0, 1.0);
    
//     // combine results
//     vec3 ambient = light.ambient * texture(material.diffuse, iTexture);
//     vec3 diffuse = light.diffuse * diff * texture(material.diffuse, iTexture);
//     vec3 specular = light.specular * spec * texture(material.specular, iTexture);
//     ambient *= attenuation * intensity;
//     diffuse *= attenuation * intensity;
//     specular *= attenuation * intensity;
//     return (ambient + diffuse + specular);
// }

//
void main()
{
    vec4 result = vec4(0.0f, 0.0f, 0.0f, 1.0f);
    vec3 normal = normalize(iNormal);
    vec3 viewDirection = normalize(viewPosition - iPosition);

    // for (int i = 0; i < pointLights.lights.length(); i++)
    // {    
    //     result += computePointLight(pointLights.lights[i], normal, viewDirection, iPosition);
    // }

    // for (int i = 0; i < directionLights.lights.length(); i++)
    // {    
    //     result += computeDirectionLight(directionLights.lights[i], normal, viewDirection, iPosition);
    // }
    
    // for (int i = 0; i < spotLights.lights.length(); i++)
    // {    
    //     result += computeSpotLight(spotLights.lights[i], normal, viewDirection, iPosition);
    // }

    oColor = result * texture(stexture, iTexture);
}
