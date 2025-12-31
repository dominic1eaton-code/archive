
/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#pragma once

#ifndef vulkan_exec_h
#define vulkan_exec_h

#include "vulkan_scene.h"
#include "vulkan_model.h"
#include "vulkan_shader.h"
#include "Ogun/Sync/VFence.h"
#include "Ogun/Sync/VSemaphore.h"
#include "Ogun/Buffer/VSwapchain.h"

namespace ogun
{

struct OImage
{
    std::string file;

    VkSampler sampler;

    /**
     * @brief depth image
     */
    VkImage image;

    /**
     * @brief texture image memory
     */
    VkDeviceMemory memory;
    
    /**
     * @brief texture image view
     */
    VkImageView view;

    uint32_t mipLevels;

    glm::vec2 extent;
    
};


class TestShader0;
class TerrainShader;

class WindowInfo
{
public:
    /**
     * @brief constructor
     */
    WindowInfo()
    {}

    /**
     * @brief handle to window
     */
    HWND hwnd;

    /**
     * @brief name of window
     */
    std::string name;

    /**
     * @brief window height in px
     */
    uint32_t height;

    /**
     * @brief window width in px
     */
    uint32_t width;
};

struct VulkanModelInfo
{
public:
    VulkanModelInfo()
    {}

    /**
     * @brief window info
     */
    WindowInfo window;

    /**
     * @brief root mount of filesystem
     */
    std::string mount;
};

class VulkanModel
{
public:

    VulkanModel();

    virtual ~VulkanModel(void) = default;

    /**
     * @brief initialize vulkan model
     * @param info model info
     */
    void init(VulkanModelInfo info);
    
    /**
     * @brief begin model
     */
    void begin();

    /**
     * @brief draw frame
     */
    void draw(float tick);

    /**
     * @brief shutdown model
     */
    void shutdown();
        
    /**
     * @brief handle cursor input
     * @param xpos x position of cursor in px
     * @param ypos y position of cursor in px
     */
    void handleCursor(float xpos, float ypos);

    /**
     * @brief handle mouse movement input
     * @param xpos x position of cursor in px
     * @param ypos y position of cursor in px
     */
    void handleMouse(double xpos, double ypos);

    /**
     * @brief recompile shaders
     */
    void recompileShaders();

    /**
     * @brief transform camera 
     * @param angle rotation angle
     * @param axis axis of transform
     * @param type type of transform
     */
    void transform(float angle, glm::vec3 axis, uint32_t type = 0);

    /**
     * @brief move camera
     * @param angle  movement
     * @param axis axis of transform
     */
    void move(float angle, glm::vec3 axis);

    /**
     * @brief rotate camera
     * @param angle rotation
     * @param axis axis of transform
     */
    void rotate(float angle, glm::vec3 axis);

    /**
     * @brief change size of framebuffer
     * @param width new width
     * @param height new height
     */
    void resizeFramebuffer(uint32_t width, uint32_t height);

    /**
     * @brief rebuild swapchain
     */
    void rebuildSwapchain();

    /**
     * @brief cleanup old swapchain
     */
    void cleanupSwapchain();

    /**
     * @brief create new swapchain
     */
    void createSwapchain();

    /**
     * @brief rebuild pipeline if vertex polygon mode changed
     */
    void rebuildPipeline(VkPolygonMode mode);

    /**
     * @brief rebuild pipeline if shaders reloaded
     */
    void rebuildPipeline(std::vector<VShader> shaders);

    void translateObject(uint32_t object_index, glm::vec3 translation,  bool bflip = false);

    void moveObject(glm::vec3 transform);

    void switchActiveObject();

protected:

    /**
     * @brief get swapchain support details
     */
    SwapChainSupportDetails querySwapchainSupport(VkPhysicalDevice device, VkSurfaceKHR surface);

private:
    std::vector<bool> bUpdateRecordCommands;

    uint32_t m_currentActiveObjectIndex = 0;

    glm::vec3 obj_transform;

    VScene* m_scene;

    /**
     * @brief position of cursor on screen
     */
    glm::vec2 m_cursorPosition;

    /**
     * @brief mouse moved for the first time?
     */
    bool firstMouse = true;

    /**
     * @brief previous cursor position x
     */
    float lastX;
    
    /**
     * @brief previous cursor position y
     */
    float lastY;
    
    /**
     * @brief camera yaw
     */
    float yaw = 0.0f;
    
    /**
     * @brief camera pitch
     */
    float pitch = 0.0f;
    
    /**
     * @brief camera roll
     */
    float roll = 0.0f;

    /**
     * @brief camera position
     */
    glm::vec3 cameraPos = glm::vec3(20.0f, 20.0f, 20.0f);
    
    /**
     * @brief camera front face position
     */
    glm::vec3 cameraFront = glm::vec3(0, 1.0f, 0.0f);

    /**
     * @brief camera angle
     */
    glm::vec3 cameraUp    = glm::vec3(0.0, 0.0, 1.0f);

    
    /**
     * @brief camera movement speed
     */
    float cameraSpeed = 2.5f;

    /**
     * @brief window udpated
     */
    bool m_update = false;

    /**
     * @brief shaders
     */
    std::vector<VShader> m_shaders;
    
    /**
     * @brief anti aliasing samples
     */
    VkSampleCountFlagBits m_msaaSamples;
    
    /**
     * @brief descriptor layout
     */
    VkDescriptorSetLayout m_descriptorSetLayout;
    
    /**
     * @brief vulkan instance
     */
    VkInstance m_instance;
    
    /**
     * @brief window surface
     */
    VkSurfaceKHR m_surface;
    
    /**
     * @brief physical device
     */
    VPhysicalDevice* m_phydevice;
    
    /**
     * @brief device queue indices
     */
    QueueFamilyIndices m_pindices;
    
    /**
     * @brief physical devices
     */
    VkPhysicalDevice m_pdevice;
    
    /**
     * @brief logical device info
     */
    DeviceInfo m_deviceinfo;

    OImage terrainHeightMapImage;

    /**
     * @brief texture image
     */
    VkImage m_textureImage;
    
    /**
     * @brief color image
     */
    VkImage m_colorImage;
    
    /**
     * @brief depth image
     */
    VkImage m_depthImage;

    /**
     * @brief texture image memory
     */
    VkDeviceMemory m_textureImageMemory;
    
    /**
     * @brief color image memory
     */
    VkDeviceMemory m_colorImageMemory;
    
    /**
     * @brief depth image memory
     */
    VkDeviceMemory m_depthImageMemory;
    
    /**
     * @brief texture image view
     */
    VkImageView m_textureImageView;
    
    /**
     * @brief color image view
     */
    VkImageView m_colorImageView;
    
    /**
     * @brief depth image view
     */
    VkImageView m_depthImageView;
    
    /**
     * @brief window width
     */
    uint32_t m_width;
    
    /**
     * @brief window height
     */
    uint32_t m_height;

    /**
     * @brief is window framebuffer resized?
     */
    bool m_framebufferResized;

    // camera transform data
    /**
     * @brief camera rotation angle
     */
    float m_angle;
    
    /**
     * @brief camera rotation angle axis
     */
    glm::vec3 m_axis;
    
    /**
     * @brief camera movement
     */
    float m_move;

    /**
     * @brief phsyical device memory properties
     */
    VkPhysicalDeviceMemoryProperties m_memProperties;

    /**
     * @brief vulkan command pool
     */
    VkCommandPool m_commandPool;

    /**
     * @brief mesh vertices
     */
    std::vector<TVertex> m_vertices{};

    /**
     * @brief mesh indices
     */
    std::vector<uint16_t> m_indices{};

    /**
     * @brief vulkan descriptor sets
     */
    std::vector<VkDescriptorSet> m_descriptorSets;

    /**
     * @brief index of current frame in flight
     */
    uint32_t m_frameIndex;

    /**
     * @brief logical device
     */
    VkDevice m_device;

    /**
     * @brief frame fences
     */
    VFences* m_fences;

    /**
     * @brief frame semaphores
     */
    VSemaphores* m_semaphores;

    /**
     * @brief current swapchain
     */
    VSwapchain m_swapchain;

    /**
     * @brief Shader
     */
    TerrainShader* m_shader;

    /**
     * @brief device queues
     */
    std::vector<VkQueue> m_queues;
    
    /**
     * @brief vulkan command buffers
     */
    std::vector<VkCommandBuffer> m_commandBuffers;

    /**
     * @brief render pass
     */
    VkRenderPass m_renderpass;
    
    /**
     * @brief frame buffers
     */
    std::vector<VkFramebuffer> m_framebuffers;
    
    /**
     * @brief graphics pipelines
     */
    std::vector<VkPipeline> m_pipelines;
    
    /**
     * @brief mesh vertex buffers
     */
    std::vector<VkBuffer> m_vertexBuffers;
       /**
     * @brief mesh index buffer
     */
    VkBuffer m_indexBuffer;
    
    /**
     * @brief pipeline layout
     */
    VkPipelineLayout m_layout;

    /**
     * @brief total number of indices in index buffer
     */
    uint32_t m_indicesCount;

   /**
     * @brief total number of vertices in vertex buffer
     */
    uint32_t m_vertsCount;

};

}; // namespace ogun

#endif // vulkan_exec_h