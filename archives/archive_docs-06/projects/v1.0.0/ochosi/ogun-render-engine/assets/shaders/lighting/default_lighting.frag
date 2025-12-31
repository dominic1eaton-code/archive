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

vec4 compute_lighting(vec3 view_position, vec3 norm, int lighting_type);
vec4 compute_kernel();
vec4 compute_light_casting(GPULightData light, vec3 normal, vec3 viewdir);
vec4 compute_phong_lighting(bool blinn, sampler2D material_texture, GPULightData light, vec3 view_position, vec3 norm);
vec4 compute_plot(float u_resolution);
const float offset = 1.0 / 300.0;

void main()
{
    vec4 result = vec4(0.0f);
    result += compute_lighting(vec3(scene.view.x, scene.view.y, scene.view.z), normalize(inormal), 0);
    result += compute_kernel();
    // ocolor = compute_plot(600*800);
    ocolor = result;
}

float plot(vec2 st, float pct)
{
    return smoothstep( pct-0.02, pct, st.y) -
           smoothstep( pct, pct+0.02, st.y);
}

vec4 compute_plot(float u_resolution)
{
    vec2 st = gl_FragCoord.xy/u_resolution;
    // Smooth interpolation between 0.1 and 0.9
    float y = smoothstep(0.1,0.9,st.x);
    vec3 color = vec3(y);
    float pct = plot(st,y);
    color = (1.0-pct)*color+pct*vec3(0.0,1.0,0.0);
    return vec4(color,1.0);
}

vec4 compute_lighting(vec3 view_position, vec3 norm, int lighting_type)
{
    // vec3 norm = normalize(inormal);
    vec3 view_direction = normalize(vec3(view_position.x, view_position.y, view_position.z) - iposition);
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
        if (lighting_type == 0)
            result += compute_light_casting(lights.data[l], norm, view_direction) * material;
        else
            result += compute_phong_lighting(false, materials[textureID], lights.data[l], view_position, norm);
    }
    return result;
    // ocolor = icolor;
    // ocolor = material;
}

vec4 compute_kernel()
{
    // test kernels
    vec2 offsets[9] = vec2[](
        vec2(-offset,  offset), // top-left
        vec2( 0.0f,    offset), // top-center
        vec2( offset,  offset), // top-right
        vec2(-offset,  0.0f),   // center-left
        vec2( 0.0f,    0.0f),   // center-center
        vec2( offset,  0.0f),   // center-right
        vec2(-offset, -offset), // bottom-left
        vec2( 0.0f,   -offset), // bottom-center
        vec2( offset, -offset)  // bottom-right
    );
    float sharpen_kernel[9] = float[](
        -1, -1, -1,
        -1,  9, -1,
        -1, -1, -1
    );
    float blur_kernel[9] = float[](
        1.0 / 16, 2.0 / 16, 1.0 / 16,
        2.0 / 16, 4.0 / 16, 2.0 / 16,
        1.0 / 16, 2.0 / 16, 1.0 / 16  
    );
    float edge_kernel[9] = float[](
        1,  1,  1,
        1, -8,  1,
        1,  1,  1
    );
   vec3 sampleTex[9];
    for(int i = 0; i < 9; i++)
    {
        sampleTex[i] = vec3(texture(materials[1], itexture.st + offsets[i]));
    }
    vec3 col = vec3(0.0);
    for(int i = 0; i < 9; i++)
        col += sampleTex[i] * blur_kernel[i] * edge_kernel[i]; // kernel[i]
    return vec4(col, 1.0);
}

vec4 compute_light_casting(GPULightData light, vec3 normal, vec3 viewdir)
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

vec4 compute_phong_lighting(bool blinn, sampler2D material_texture, GPULightData light, vec3 view_position, vec3 norm)
{
    vec3 color = texture(material_texture, itexture.xy).rgb * normalize(light.ambient.xyz);
    // ambient
    float ambient_multiplier = 0.05;
    vec3 ambient = ambient_multiplier * color;
    // diffuse
    vec3 lightDir = normalize(light.position.xyz - iposition);
    vec3 normal = norm;
    float diff = max(dot(lightDir, normal), 0.0);
    vec3 diffuse = diff * color;
    // specular
    vec3 viewDir = normalize(view_position - iposition);
    vec3 reflectDir = reflect(-lightDir, normal);
    float spec = 0.0;
    if(blinn)
    {
        vec3 halfwayDir = normalize(lightDir + viewDir);
        spec = pow(max(dot(normal, halfwayDir), 0.0), 32.0);
    }
    else
    {
        vec3 reflectDir = reflect(-lightDir, normal);
        spec = pow(max(dot(viewDir, reflectDir), 0.0), 8.0);
    }
    vec3 specular = vec3(0.3) * spec; // assuming bright white light color
    // vec3 specular = normalize(light.ambient.xyz) * spec; // assuming bright white light color
    return vec4(ambient + diffuse + specular, 1.0);
}