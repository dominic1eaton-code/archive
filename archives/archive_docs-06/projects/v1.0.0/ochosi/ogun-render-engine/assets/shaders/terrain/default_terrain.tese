// @copyright
// @brief
// @note 
#version 460

layout(quads, fractional_odd_spacing, ccw) in;
layout(location = 0) in vec2 TextureCoord[];
layout(location = 0) out float Height;

layout(binding = 1) uniform GPUCamera
{
    mat4 model;
    mat4 view;
    mat4 proj;
} camera;

// layout(binding = 1) uniform GPUTerrain
// {
//     vec4 parameters;
// } terrain;

layout(binding = 2) uniform sampler2D height_map;

void main()
{
    // float max_tesselation_level = terrain.parameters[0];
    // float tesselation_offset = terrain.parameters[1];
    float max_tesselation_level = 64.0f;
    float tesselation_offset = 16.0f;

    // patch coordinates
    float u = gl_TessCoord.x;
    float v = gl_TessCoord.y;

    // control point texture coordinates
    vec2 t00 = TextureCoord[0];
    vec2 t01 = TextureCoord[1];
    vec2 t10 = TextureCoord[2];
    vec2 t11 = TextureCoord[3];

    // bilinear interpolate texture coordinate across patch
    vec2 t0 = (t01 - t00) * u + t00;
    vec2 t1 = (t11 - t10) * u + t10;
    vec2 texCoord = (t1 - t0) * v + t0;

    // texel at patch coordinate for height and scale+shift
    Height = texture(height_map, texCoord).y * max_tesselation_level - tesselation_offset;

    // control point position coordinates
    vec4 p00 = gl_in[0].gl_Position;
    vec4 p01 = gl_in[1].gl_Position;
    vec4 p10 = gl_in[2].gl_Position;
    vec4 p11 = gl_in[3].gl_Position;

    // compute patch surface normal
    vec4 uVec = p01 - p00;
    vec4 vVec = p10 - p00;
    vec4 normal = normalize( vec4(cross(vVec.xyz, uVec.xyz), 0) );

    // bilinear interpolate position coordinate accorss patch
    vec4 p0 = (p01 - p00) * u + p00;
    vec4 p1 = (p11 - p10) * u + p10;
    vec4 p = (p1 - p0) * v + p0 + normal * Height;

    // displace point along normal
    p += normal * Height;

    // output patch point position in clip space
    gl_Position = camera.proj * camera.view * camera.model * p;
}