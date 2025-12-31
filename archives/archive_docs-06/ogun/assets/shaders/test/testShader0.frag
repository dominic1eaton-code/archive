// @header
// @copyright
// @brief
// @note 
#version 450

//

layout(location = 0) in vec4 iColor;
layout(location = 1) in vec2 iTexture;
// layout(location = 2) in vec3 iNormal;

//
layout(location = 0) out vec4 oColor;

//
layout(binding = 2) uniform sampler2D texSampler;

void main()
{
    // oColor = iColor;
    oColor = texture(texSampler, iTexture);
}
