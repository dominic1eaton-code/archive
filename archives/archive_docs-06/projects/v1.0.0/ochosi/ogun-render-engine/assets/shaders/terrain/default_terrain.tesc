// @copyright
// @brief
// @note 
#version 460

layout(location = 0) in vec2 TexCoord[];
layout(location = 0) out vec2 TextureCoord[];
layout(vertices = 4) out;

layout(binding = 0) uniform GPUCamera2
{
    mat4 model;
    mat4 view;
} camera2;

// layout(binding = 1) uniform GPUTerrain
// {
//     vec4 parameters;
// } terrain;

void main()
{
    /* specify patch data */
    // vertex attributes
    gl_out[gl_InvocationID].gl_Position = gl_in[gl_InvocationID].gl_Position;
    TextureCoord[gl_InvocationID] = TexCoord[gl_InvocationID];

    /* specify tesselation */
    // tesselation level for entire patch
    if(gl_InvocationID == 0)
    {
        // const int MIN_TESS_LEVEL = terrain.parameters[0];
        // const int MAX_TESS_LEVEL = terrain.parameters[1];
        // const float MIN_DISTANCE = terrain.parameters[2];
        // const float MAX_DISTANCE = terrain.parameters[3];
        const int MIN_TESS_LEVEL = 4;
        const int MAX_TESS_LEVEL = 64;
        const float MIN_DISTANCE = 20;
        const float MAX_DISTANCE = 800;

        vec4 eyeSpacePos00 = camera2.view * camera2.model * gl_in[0].gl_Position;
        vec4 eyeSpacePos01 = camera2.view * camera2.model * gl_in[1].gl_Position;
        vec4 eyeSpacePos10 = camera2.view * camera2.model * gl_in[2].gl_Position;
        vec4 eyeSpacePos11 = camera2.view * camera2.model * gl_in[3].gl_Position;

        // "distance" from camera scaled between 0 and 1
        float distance00 = clamp( (abs(eyeSpacePos00.z) - MIN_DISTANCE) / (MAX_DISTANCE-MIN_DISTANCE), 0.0, 1.0 );
        float distance01 = clamp( (abs(eyeSpacePos01.z) - MIN_DISTANCE) / (MAX_DISTANCE-MIN_DISTANCE), 0.0, 1.0 );
        float distance10 = clamp( (abs(eyeSpacePos10.z) - MIN_DISTANCE) / (MAX_DISTANCE-MIN_DISTANCE), 0.0, 1.0 );
        float distance11 = clamp( (abs(eyeSpacePos11.z) - MIN_DISTANCE) / (MAX_DISTANCE-MIN_DISTANCE), 0.0, 1.0 );

        float tessLevel0 = mix( MAX_TESS_LEVEL, MIN_TESS_LEVEL, min(distance10, distance00) );
        float tessLevel1 = mix( MAX_TESS_LEVEL, MIN_TESS_LEVEL, min(distance00, distance01) );
        float tessLevel2 = mix( MAX_TESS_LEVEL, MIN_TESS_LEVEL, min(distance01, distance11) );
        float tessLevel3 = mix( MAX_TESS_LEVEL, MIN_TESS_LEVEL, min(distance11, distance10) );

        gl_TessLevelOuter[0] = tessLevel0;
        gl_TessLevelOuter[1] = tessLevel1;
        gl_TessLevelOuter[2] = tessLevel2;
        gl_TessLevelOuter[3] = tessLevel3;

        gl_TessLevelInner[0] = max(tessLevel1, tessLevel3);
        gl_TessLevelInner[1] = max(tessLevel0, tessLevel2);
    }
}
