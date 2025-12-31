/**
 * @copyright
 * @brief
 * @note
 */

 #pragma once
 #ifndef vulkan_scene_h
 #define vulkan_scene_h
 
namespace vulkan
{

struct VBrush
{

};

void select_active_object(uint32_t objectID);
void translate_active_object(glm::vec3 translation);
 
void zoom_camera(ogun::VCamera& camera, float rotation);
void translate_camera(uint32_t cameraID, float translation, glm::vec3 axix, uint32_t dimension);
void rotate_camera(uint32_t cameraID, float rotation);

// void translate_object(uint32_t object_index, glm::vec3 translation, bool bflip)
void rotate_object();
void scale_object();
void edit_object(uint32_t id, VBrush brush);

};

#endif // vulkan_scene_h