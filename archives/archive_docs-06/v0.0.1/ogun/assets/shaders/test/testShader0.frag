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

// layout(binding = 3) uniform GPUView
// {
//     vec4 position;
// } view;

struct DirLight
{
    vec4 direction;
    vec4 ambient;
    vec4 diffuse;
    vec4 specular;
};


// layout(std140, binding = 4) buffer DirectionalLight
// {
//     DirLight light[];
// } dirLight;

// layout(binding = 5) uniform GPUMaterial
// {
//     float shininess;
// } material;

// layout(binding = 6) uniform sampler2D texsampler;
// layout(binding = 7) uniform sampler2D texdiffuse;
// layout(binding = 8) uniform sampler2D texspecular;

// vec4 colors[3] = vec4[](
//     vec4(1.0, 0.0, 0.0, 1.0),
//     vec4(0.0, 1.0, 0.0, 1.0),
//     vec4(0.0, 0.0, 1.0, 1.0)
// );

vec4 CalcDirLight(DirLight light, float shine, vec3 normal, vec3 viewDir);

void main()
{
    vec3 norm = normalize(iNormal);
    // vec3 viewDir = normalize(vec3(view.position.x, view.position.y, view.position.z) - iPosition);

    // compute lighting
    DirLight light0;
    light0.ambient = vec4(0.5, 0.5, 0.5, 1.0);
    light0.diffuse = vec4(0.4, 0.4, 0.4, 1.0);
    light0.specular = vec4(0.5, 0.5, 0.5, 1.0);
    light0.direction = vec4(-0.2f, -1.0f, -0.3f, 1.0);
    // vec4 result = CalcDirLight(light0, norm, viewDir);
    // vec4 result = CalcDirLight(dirLight.light[iInstance], norm, viewDir);
    vec4 result = vec4(1.0, 0.0, 0.0, 1.0);

    // oColor = iColor;
    // oColor = result * texture(texsampler, iTexture);
    oColor = texture(texsampler, iTexture);
}

// calculates the color when using a directional light.
vec4 CalcDirLight(DirLight light, float shine, vec3 normal, vec3 viewDir)
{
    vec3 lightDir = normalize(-vec3(light.direction.x, light.direction.y, light.direction.z));
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
