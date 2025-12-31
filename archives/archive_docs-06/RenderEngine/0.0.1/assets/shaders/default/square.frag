#version 450
// @brief   Default fragment shader
// @note    N/A
// @version 0.1
// @copyright Copyright (c) 2023
// input
layout(location = 0) in vec3 fragColor;

// output
layout(location = 0) out vec4 outColor;

// called for every fragment
void main()
{
    outColor = vec4(fragColor, 1.0);
}
