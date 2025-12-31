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

//
layout(location = 0) out vec4 oColor;
layout(location = 1) out vec4 oPrimitiveID;

//
layout(binding = 2) uniform sampler2D texsampler;

layout(binding = 3) uniform GPUView
{
    vec4 position;
} view;


struct LightParameters
{
    float k0;
    float k1;
    float k2;
};

struct LightData
{
    vec4 direction;
    vec4 ambient;
    vec4 diffuse;
    vec4 specular;
};

struct Light
{
    LightData data;
    LightParameters parameters;
};

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

// layout(binding = 4) uniform sampler2D texdiffuse[];

layout(binding = 4) uniform GPUCursor
{
    vec4 position;
} cursor;

/* https://blog.gavs.space/post/003-vulkan-mouse-picking/ */
#define DEPTH_ARRAY_SCALE 32
layout(std140, binding = 5) buffer writeonly GPUSelector
{
    float data[DEPTH_ARRAY_SCALE];
} selector;


// layout(binding = 6) uniform OPixel
// {
//     vec4 ocolor;
// } opixel;

// layout(std140, binding = 1) buffer GPUMesh
// {
//     GPUMeshData models[];
// } meshes;

vec4 CalcDirLight(DirLight light, float shine, vec3 normal, vec3 viewDir);
vec4 CalcPointLight(PointLight light, vec3 normal, vec3 fragPos, vec3 viewDir, float shine);

void main()
{
    vec3 norm = normalize(iNormal);
    vec3 viewDir = normalize(vec3(view.position.x, view.position.y, view.position.z) - iPosition);
    vec4 result = vec4(0.0, 0.0, 0.0, 1.0);
    float shine = .1;

    // compute lighting
    // DirLight light0;
    // light0.ambient = vec4(1.0, 1.0, 1.0, 1.0);
    // light0.diffuse = vec4(1.0, 1.0, 1.0, 1.0);
    // light0.specular = vec4(1.0, 1.0, 1.0, 1.0);
    // light0.direction = vec4(-10.5f, -10.0f, 10.0f, 1.0);
    // result += CalcDirLight(light0, shine, norm, viewDir);
    // vec4 result = CalcDirLight(dirLight.light[iInstance], norm, viewDir);
    
    PointLight plight0;
    plight0.position = vec4(0.0, 0.0, 0.0, 1.0f);
    plight0.ambient = vec4(80.0f, 180.0f, 180.0f, 1.0f);
    plight0.diffuse = vec4(0.8f, 0.8f, 0.8f, 1.0f);
    plight0.specular = vec4(0.5f, 0.5f, 0.5f, 1.0f);
    plight0.k0 = 0.1f;
    plight0.k1 = 30.0f;
    plight0.k2 = 20.0f;
    // plight0.k1 = iPosition.x;//float(view.position.x) / 10; //20.0; //cursor.position.x;// / 10;
    // plight0.k2 = .2;
    result += CalcPointLight(plight0, norm, iPosition, viewDir, shine);

    float depth = gl_FragCoord.z;
    float near = 0.1;
    float far  = 100.0;
    float ndc = depth * 2.0 - 1.0;
    float linearDepth = (2.0 * near * far) / (far + near - ndc * (far - near));
    float dd = linearDepth / far;
    vec3 d = vec3(dd*2, 0.0, 0.0);

    /* fragment selection */
    vec2 cpos_color;
    cpos_color.x = ((view.position.x + 1) / 2);
    cpos_color.y = (view.position.y + 1) / 2;
    vec2 gfrag;
    gfrag.x =  (gl_FragCoord.x / 600);
    if (gl_PrimitiveID == 0 || gl_PrimitiveID == 1 ||
        gl_PrimitiveID == 2 || gl_PrimitiveID == 3 ||
        gl_PrimitiveID == 4 || gl_PrimitiveID == 5 ||
        gl_PrimitiveID == 6 || gl_PrimitiveID == 7 ||
        gl_PrimitiveID == 8 || gl_PrimitiveID == 9 ||
        gl_PrimitiveID == 10 || gl_PrimitiveID == 11)
    {
        oColor = vec4(1, 1, 0, 1.0);
    }
    else
    {
        oColor = result * texture(texsampler, iTexture);
    }
    oPrimitiveID = vec4(gl_PrimitiveID / (7*12), 0.0, 0.0, 0.0);
    uint zindex = uint(gl_FragCoord.z * DEPTH_ARRAY_SCALE);
    float selection_threshhold = .7075;
    if(length(view.position.xy - gl_FragCoord.xy) < selection_threshhold)
    {
        selector.data[zindex] = gl_FragCoord.z; //view.position.z;
    }
    // for (int i = 0; i < DEPTH_ARRAY_SCALE; i++)
    // {
    //      selector.data[i] = 0;
    // }
    // selector.data[3] =  11;
    // selector.data[2] =  9;
    // selector.data[1] =  0;
    // selector.data[0] =  0; //view.position.x ;// length(view.position.xy - gl_FragCoord.xy);
    // opixel.color = vec4(1.0, 1.0, gl_PrimitiveID, 1.0f);
    // oColor = vec4(d, 1.0);// * texture(texsampler, iTexture);
    // oColor = result * iColor * texture(texsampler, iTexture);
    // oColor = iColor;
    // oPrimitiveID = vec4(gl_PrimitiveID / (7*12), 0.0, 0.0, 0.0);
    // oPrimitiveID = vec4(gl_PrimitiveID / (7*12), 0.0, 0.0, 1.0);
    // oPrimitiveID = vec4(gl_PrimitiveID / (10), 0.0, 0.0, 1.0);
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
