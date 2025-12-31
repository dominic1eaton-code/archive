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

struct TVertex;

struct VBuffer
{
    VkBuffer buffer;

    VkDeviceMemory memory;

    void* data;

    void create(size_t size)
    {
    }

    template<typename T>
    void copy(VBuffer sbuffer, std::vector<T> cdata)
    {

    }

    void update()
    {

    }
};

struct VBufferSet
{
    std::vector<VBuffer> set;
};

struct Descriptor
{

    std::vector<VkDescriptorSet> sets;

    VkDescriptorSetLayout layout;

    VkDescriptorPool pool;
};

struct Texture
{
    VkSampler sampler;

    VkImageView view;

    VkFormat format;

    VkImageLayout layout;
};

struct OShader
{
    std::string name;
    std::string type;
    std::string ext;
    VkShaderStageFlagBits stage;
};

struct ShaderBinding
{
    VBuffer buffer;

    Texture texture;
};

class TerrainShader
{
public:
    TerrainShader() = default;
    virtual ~TerrainShader(void) = default;

    std::vector<VkBuffer> vertexBuffers() const { return m_vertexBuffers; }
    
    VkBuffer indexBuffer() const { return m_indexBuffer; }

    // std::vector<Descriptor> descriptors() const { return m_descriptors; }
    std::vector<VkDescriptorSet> descriptorSets() const { return m_descriptor.sets; }
    
    VkDescriptorSetLayout layout() const { return m_descriptor.layout; }

    std::vector<VShader> shaders() const { return m_shaders; }

    void init(VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties, VkDevice device,
                std::string shaderPath);

    void load(std::vector<TVertex> vertices, std::vector<uint16_t> indices,
              size_t camerasize, Texture terrainHeightMap);

    // template<typename T>
    // void update(std::vector<T> udata, VBuffer& vbuffer, VkDeviceSize dataIndex);
        
    void update(float tick, uint32_t currentImage, glm::mat4 view);

    void updateVertexBuffer(std::vector<TVertex> udata, VkDeviceSize dataIndex);

private:

    template<typename T>
    void createBuffers(std::vector<T> vdata);

    void createShaderModules();

    // void createVertexBuffers();

    // void createIndexBuffer();

    // void createBindingBuffers();

    void createDescriptors(Texture texture);
    
    void createVertexBuffer(std::vector<TVertex> vertices, VBuffer& vbuffer);//, VkDeviceSize buffersize);

    void createIndexBuffer(std::vector<uint16_t> indices, VBuffer& vbuffer);//, VkDeviceSize buffersize);

    void createUniformBuffers(std::vector<VBuffer>& vbuffer, VkDeviceSize buffersize);


    VBuffer stagebuffer;
    VBuffer vertexbuffer;
    VBuffer indexbuffer;
    VBuffer uniformBuffer;

    std::string m_shaderPath;

    std::vector<VkBuffer> m_vertexBuffers;

    VkBuffer m_indexBuffer;
    
    std::vector<VBuffer> m_gpuVertexBuffers;

    VBuffer m_gpuIndexBuffer;

    std::vector<VBuffer> m_gpuCameraBuffers;
    std::vector<VBuffer> m_gpuCamera2Buffers;
    
    std::vector<VBufferSet> m_gpubindingBuffers;

    std::vector<Descriptor> m_descriptors;
    Descriptor m_descriptor;

    std::vector<VShader> m_shaders;

    glm::mat4 m_model;

    VkExtent2D m_extent;

    VkDevice m_device;

    VkQueue m_queue;

    VkCommandPool m_pool;

    VkPhysicalDeviceMemoryProperties m_memProperties;

    uint32_t m_buffersetSize = constants::MAX_FRAMES_IN_FLIGHT;

};

}; // namespace ogun

#endif // vulkan_shader_h