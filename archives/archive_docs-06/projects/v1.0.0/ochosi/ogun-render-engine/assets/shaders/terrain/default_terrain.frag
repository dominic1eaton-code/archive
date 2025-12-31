// @copyright
// @brief
// @note 
#version 460

layout(location = 0) in float iheight;
layout(location = 0) out vec4 ocolor;

void main()
{
    float max_tesselation_level = 64.0f;
    float tesselation_offset = 16;
    float h = (iheight + tesselation_offset) / max_tesselation_level;
    ocolor = vec4(h, h, h, 1.0);
}