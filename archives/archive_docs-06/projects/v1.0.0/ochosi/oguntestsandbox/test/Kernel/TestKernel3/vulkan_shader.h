/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#pragma once
#ifndef vulkan_shader_h
#define vulkan_shader_h

#include "vulkan_model.h"
#include "vulkan_gpu.h"

namespace ogun
{

/**
 * @brief compute shader effect data 
 */
struct ComputePushConstants
{
    /**
     * data word 1
     */
    alignas(16) glm::vec4 data1;
    
    /**
     * data word 2
     */
    alignas(16) glm::vec4 data2;
    
    /**
     * data word 3
     */
    alignas(16) glm::vec4 data3;
    
    /**
     * data word 4
     */
    alignas(16) glm::vec4 data4;
};

/**
 * @brief compute shader effect state
 */
struct ComputeEffect 
{
    /**
     * name of shader effect
     */
    const char* name;

    /**
     * associated compute pipeline
     */
    VkPipeline pipeline;

    /**
     * associated compute pipeline layout
     */
    VkPipelineLayout layout;

    /**
     * shader data
     */
    ComputePushConstants data;
};

/**
 * @brief shader type
 */
enum class ShaderType
{
    VERTEX,
    FRAGMENT,
    GEOMETRY,
    COMPUTE,
    TESSELATION
};


struct VBuffer
{
    VkBuffer buffer;

    VkDeviceMemory memory;

    void* data;
};

class TestShader0
{
public:
    TestShader0();
    virtual ~TestShader0(void) = default;

    std::vector<VkBuffer> vertexBuffers() const { return m_vertexBuffers; }
    
    VkBuffer indexBuffer() const { return m_indexBuffer; }

    std::vector<VkDescriptorSet> descriptorSets() const { return m_descriptorSets; }

    void load(std::vector<VertexShaderData> vertices, std::vector<uint16_t> indices, std::vector<GPUMeshData> meshes, std::vector<GPUDirLight> dirlights,
                VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties, VkDevice device, VkExtent2D extent,
                VkDescriptorSetLayout& descriptorSetLayout, VkSampler textureSampler, VkImageView textureImageView, VkImageLayout imageLayout,
                std::string shaderPath);

    template<typename T>
    void updateBuffer(std::vector<T> udata, VBuffer& vbuffer, VkDeviceSize dataIndex);

    /**
     * update vertex buffer data
     * @param udata new data to write to vertex buffer
     * @param dataIndex offset to vertex buffer to write to
     */
    void updateVertexBuffer(std::vector<VertexShaderData> udata, VkDeviceSize dataIndex);

    void updateStorageBuffer();

    void update(float tick, uint32_t currentImage, glm::mat4 view, glm::vec2 gcursor);

    void createVertexBuffer(std::vector<VertexShaderData> vertices, VBuffer& vbuffer);//, VkDeviceSize buffersize);

    void createIndexBuffer(std::vector<uint16_t> indices, VBuffer& vbuffer);//, VkDeviceSize buffersize);

    void createUniformBuffers(std::vector<VBuffer>& vbuffer, VkDeviceSize buffersize);

    template<typename T>
    void createStorageBuffers(std::vector<T> vdata, std::vector<VBuffer>& vbuffer, VkDeviceSize buffersize);

    void createDescriptorPool();

    void createDescriptorSetLayout();

    void createDescriptorSets(VkSampler textureSampler, VkImageView textureImageView, VkImageLayout imageLayout,
                                uint32_t numMeshes, uint32_t numDirLights);
    
    std::vector<VShader> shaders() const { return m_shaders; }

private:

    glm::mat4 m_modelMatrix;

    std::vector<VShader> m_shaders;

    std::vector<VkBuffer> m_vertexBuffers;

    VkBuffer m_indexBuffer;

    std::vector<VkDescriptorSet> m_descriptorSets;

    VkDescriptorSetLayout m_descriptorSetLayout;

    VkDescriptorPool m_descriptorPool;

    VkExtent2D m_extent;

    std::vector<VBuffer> m_gpuVertexBuffers;

    VBuffer m_gpuIndexBuffer;

    std::vector<VBuffer> m_gpuCameraBuffers;

    std::vector<VBuffer> m_gpuMeshBuffers;

    std::vector<VBuffer> m_gpuViewBuffers;

    std::vector<VBuffer> m_cursorViewBuffers;

    std::vector<VBuffer> m_gpuDirLightBuffers;

    std::vector<VBuffer> m_gpuMaterialBuffers;
    
    std::vector<VBuffer> m_gpuSelectorBuffers;

    VkDevice m_device;

    VkQueue m_queue;

    VkCommandPool m_pool;

    VkPhysicalDeviceMemoryProperties m_memProperties;

    uint32_t m_buffersetSize = constants::MAX_FRAMES_IN_FLIGHT;

};

}; // namespace ogun

#endif // vulkan_shader_h