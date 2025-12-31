/**
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_terrain.h"
// #include "vulkan_model.h"
#include <vulkan/vulkan.h>
#include "stb_image.h"

namespace ogun
{

void VTerrain::loadHeightMap(uint32_t width, uint32_t height)
{
    uint8_t resolution = 5u;
    glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    int8_t direction = -1;
    for (uint32_t i = 0; i < resolution-1; i++)
    {
        for (uint32_t j = 0; j < resolution-1; j++)
        {
            TVertex vquad0;
            vquad0.position.x = (direction*(width / 2.0f)) + width*i/(float)resolution;
            vquad0.position.z = 0.0f;
            vquad0.position.y = (direction*(height / 2.0f)) + height*j/(float)resolution;
            vquad0.color = color;
            vquad0.texture.x = i / float(resolution);
            vquad0.texture.y = j / float(resolution);

            TVertex vquad1;
            vquad1.position.x = (direction*(width / 2.0f)) + width*(i+1)/(float)resolution;
            vquad1.position.z = 0.0f;
            vquad1.position.y = (direction*(height / 2.0f)) + height*j/(float)resolution;
            vquad1.color = color;
            vquad1.texture.x = (i+1) / float(resolution);
            vquad1.texture.y = j / float(resolution);
            
            TVertex vquad2;
            vquad2.position.x = (direction*(width / 2.0f)) + width*i/(float)resolution;
            vquad2.position.z = 0.0f;
            vquad2.position.y = (direction*(height / 2.0f)) + height*(j+1)/(float)resolution;
            vquad2.color = color;
            vquad2.texture.x = i / float(resolution);
            vquad2.texture.y = (j+1) / float(resolution);
            
            TVertex vquad3;
            vquad3.position.x = (direction*(width / 2.0f) ) + width*(i+1)/(float)resolution;
            vquad3.position.z = 0.0f;
            vquad3.position.y = (direction*(height / 2.0f)) + height*(j+1)/(float)resolution;
            vquad3.color = color;
            vquad3.texture.x = (i+1) / float(resolution);
            vquad3.texture.y = (j+1) / float(resolution);

            // quad vertices
            m_vertices.push_back(vquad0);
            m_vertices.push_back(vquad1);
            m_vertices.push_back(vquad2);
            m_vertices.push_back(vquad3);
        }
    }
}

// std::vector<glm::vec3> VTerrain::loadHeightMap(std::string hm_file)
// {
//     int texWidth, texHeight, texChannels;
//     stbi_uc* pixels = stbi_load(hm_file.c_str(), &texWidth, &texHeight, &texChannels, STBI_rgb_alpha);
//     VkDeviceSize imageSize = texWidth * texHeight * 4;

//     // generate terrain vertex coordinates
//     float max_tesselation_level = 64.0f;
//     float tesselation_scale = 16.0f;
//     float tess_scale_factor = 256.0f;
//     std::vector<float> vertices;
//     std::vector<glm::vec3> vpositions;
//     float yscale = max_tesselation_level / tess_scale_factor;
//     float yshift = tesselation_scale;
//     uint16_t scale = 100u;
//     for (uint32_t i = 0; i < texHeight/scale; i++)
//     {
//         for (uint32_t j = 0; j < texWidth/scale; j++)
//         {
//             // texel for (i,j) texture coordinate
//             uint8_t* texel = pixels + (j + width*i) * texChannels;

//             // raw height at coordinate
//             uint8_t y = texel[0];

//             // // vertex
//             // vertices.push_back(-texHeight / 2.0f + i);      // v.x
//             // vertices.push_back( (int)y * yscale - yshift);  // v.y
//             // vertices.push_back(-texWidth / 2.0f + j);       // v.z
//             glm::vec3 pos {
//                 -texHeight / 2.0f + i,
//                 (int)y * yscale - yshift,
//                 -texWidth / 2.0f + j
//             };
//             vpositions.push_back(pos);
//         }
//     }
//     // free pixel data after use
//     stbi_image_free(pixels);
//     return vpositions;
// }

// void VTerrain::generateVertices()
// {
 
// for (uint8_t i = 0; i <= resolution; i++)
// {
//     for (uint8_t j = 0; j <= resolution-1; j++)
//     {
//         // v.x v.z

//         // 

//         // 

//         // 
//     }
// }

// }

};
