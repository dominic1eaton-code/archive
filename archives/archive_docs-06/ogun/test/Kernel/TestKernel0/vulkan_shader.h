/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_model.h"
#include "Ogun/Core/Vertex.h"

namespace ogun
{

enum class ShaderType
{
    VERTEX,
    FRAGMENT,
    GEOMETRY,
    COMPUTE,
    TESSELATION
};



struct GPUCamera
{
    alignas(16) glm::mat4 model;
    alignas(16) glm::mat4 view;
    alignas(16) glm::mat4 proj;
};

struct GPUMeshData
{
    //alignas(16)  glm::mat4 model;
    alignas(16) glm::vec4 position;
};

struct GPULight
{
    glm::vec4 ambient;
    glm::vec4 diffuse;
    glm::vec4 specular;
};

struct GPULightData
{
    GPULight light;
};

class TestShader0
{
public:
    TestShader0() = default;
    virtual ~TestShader0(void) = default;

    std::vector<VkBuffer> vertexBuffers() const { return m_vertexBuffers; }
    
    VkBuffer indexBuffer() const { return m_indexBuffer; }

    std::vector<VkDescriptorSet> descriptorSets() const { return m_descriptorSets; }

    void load(std::vector<VertexShaderData> vertices, std::vector<uint16_t> indices, std::vector<GPUMeshData> meshes,
              VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties, VkDevice device,
              VkDescriptorSetLayout& descriptorSetLayout, VkSampler textureSampler, VkExtent2D extent,
              VkImageView textureImageView, VkImageLayout imageLayout)
    {
        m_extent = extent;
        createVertexBuffer(vertices, device, m_vertexBuffer, m_vertexBufferMemory, queue, pool, memProperties);
        createIndexBuffer(indices, device, m_indexBuffer, m_indexBufferMemory, queue, pool, memProperties);
        createStorageBuffers(device, memProperties, meshes, m_shaderStorageBuffers, m_shaderStorageBuffersMemory, queue, pool);
        createUniformBuffers(m_uniformBuffers, m_uniformBuffersMemory, m_uniformBuffersData, device, memProperties);
        createDescriptorSetLayout(device, descriptorSetLayout);
        createDescriptorPool(device, m_descriptorPool);
        createDescriptorSets(device, m_descriptorSets, descriptorSetLayout, m_descriptorPool, m_uniformBuffers, textureSampler, textureImageView, imageLayout, m_shaderStorageBuffers, meshes.size());
    }
        
    void update(float tick, uint32_t currentImage)
    {
        GPUCamera cameraTransform;
        // cameraTransform.model = glm::rotate(glm::mat4(1.0f), glm::radians(1.0f), glm::vec3(0.0f, 0.0f, 0.1f));
        // cameraTransform.view = glm::lookAt(glm::vec3(0.0f, 0.0f, 3.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 1.0f, 0.0f));
        // cameraTransform.proj = glm::perspective(glm::radians(1.0f), m_extent.width / (float) m_extent.height, 0.1f, 1.0f);
        // cameraTransform.proj[1][1] *= -1;
        // cameraTransform.model = glm::rotate(glm::mat4(1.0f), glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
        // cameraTransform.view = glm::lookAt(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
        // cameraTransform.proj = glm::perspective(glm::radians(45.0f), m_extent.width / (float) m_extent.height, 0.1f, 10.0f);
        // cameraTransform.proj[1][1] *= -1;
        // cameraTransform.model = ;
        // cameraTransform.view = ;
        // cameraTransform.proj = ;
        cameraTransform.model = glm::rotate(glm::mat4(1.0f), tick * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
        cameraTransform.view = glm::lookAt(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
        cameraTransform.proj = glm::perspective(glm::radians(45.0f), m_extent.width / (float) m_extent.height, 0.1f, 10.0f);
        cameraTransform.proj[1][1] *= -1;
        memcpy(m_uniformBuffersData[currentImage], &cameraTransform, sizeof(cameraTransform));
    }

private:
    std::vector<VkBuffer> m_vertexBuffers;

    std::vector<VkDescriptorSet> m_descriptorSets;

    VkDescriptorSetLayout m_descriptorSetLayout;

    VkDescriptorPool m_descriptorPool;
    
    VkExtent2D m_extent;

    VkBuffer m_vertexBuffer;

    VkDeviceMemory m_vertexBufferMemory;

    VkBuffer m_indexBuffer;

    VkDeviceMemory m_indexBufferMemory;

    std::vector<VkBuffer> m_uniformBuffers;

    std::vector<VkDeviceMemory> m_uniformBuffersMemory;

    std::vector<void*> m_uniformBuffersData;

    std::vector<VkBuffer> m_shaderStorageBuffers;
    
    std::vector<VkDeviceMemory> m_shaderStorageBuffersMemory;

    void createDescriptorPool(VkDevice device, VkDescriptorPool& descriptorPool)
    {
        std::array<VkDescriptorPoolSize, 3> poolSizes{};
        poolSizes[0].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        poolSizes[0].descriptorCount = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        poolSizes[1].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        poolSizes[1].descriptorCount = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        poolSizes[2].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
        poolSizes[2].descriptorCount = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        VkDescriptorPoolCreateInfo poolInfo{};
        poolInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
        poolInfo.poolSizeCount = static_cast<uint32_t>(poolSizes.size());
        poolInfo.pPoolSizes = poolSizes.data();
        poolInfo.maxSets = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        if (vkCreateDescriptorPool(device, &poolInfo, nullptr, &descriptorPool) != VK_SUCCESS) {
            throw std::runtime_error("failed to create descriptor pool!");
        }
    }
    
    void createDescriptorSetLayout(VkDevice m_device, VkDescriptorSetLayout& descriptorSetLayout)
    {
        VObject<int> obj;
        VkDescriptorSetLayoutBinding cameraBinding{};
        cameraBinding.binding = 0;
        cameraBinding.descriptorCount = 1;
        cameraBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        cameraBinding.pImmutableSamplers = nullptr;
        cameraBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;

        VkDescriptorSetLayoutBinding meshBinding{};
        meshBinding.binding = 1;
        meshBinding.descriptorCount = 1;
        meshBinding.descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        meshBinding.pImmutableSamplers = nullptr;
        meshBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;

        VkDescriptorSetLayoutBinding textureBinding{};
        textureBinding.binding = 2;
        textureBinding.descriptorCount = 1;
        textureBinding.descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
        textureBinding.pImmutableSamplers = nullptr;
        textureBinding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

        std::vector<VkDescriptorSetLayoutBinding> uboLayoutBindings;
        uboLayoutBindings.push_back(cameraBinding);
        uboLayoutBindings.push_back(meshBinding);
        uboLayoutBindings.push_back(textureBinding);

        // descriptor layout
        VkDescriptorSetLayoutCreateInfo layoutInfo{};
        layoutInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
        layoutInfo.flags = 0;
        layoutInfo.pNext = nullptr;
        layoutInfo.bindingCount = uboLayoutBindings.size();
        layoutInfo.pBindings = uboLayoutBindings.data();

        // create vulkan object
        obj.createVk(vkCreateDescriptorSetLayout(m_device,
                                            &layoutInfo,
                                            nullptr,
                                            &descriptorSetLayout));
    }

    void createDescriptorSets(VkDevice& device, std::vector<VkDescriptorSet>& descriptorSets, VkDescriptorSetLayout& descriptorSetLayout, VkDescriptorPool descriptorPool,
                            std::vector<VkBuffer>& uniformBuffers, VkSampler textureSampler, VkImageView textureImageView, VkImageLayout imageLayout, std::vector<VkBuffer>& shaderStorageBuffers,
                            uint32_t numMeshes)
    {
        
        VObject<int> obj;
        std::vector<VkDescriptorSetLayout> layouts(ogun::constants::MAX_FRAMES_IN_FLIGHT, descriptorSetLayout);
        VkDescriptorSetAllocateInfo allocInfo{};
        allocInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
        allocInfo.descriptorPool = descriptorPool;
        allocInfo.descriptorSetCount = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        allocInfo.pSetLayouts = layouts.data();

        descriptorSets.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        obj.createVk(vkAllocateDescriptorSets(device,
                                        &allocInfo,
                                        descriptorSets.data()));

        for (size_t i = 0; i < ogun::constants::MAX_FRAMES_IN_FLIGHT; i++) 
        {
            std::array<VkWriteDescriptorSet, 3> descriptorWrites{};

            VkDescriptorBufferInfo bufferInfo{};
            bufferInfo.buffer = uniformBuffers[i];
            bufferInfo.offset = 0;
            bufferInfo.range = sizeof(GPUCamera);
            descriptorWrites[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
            descriptorWrites[0].dstSet = descriptorSets[i];
            descriptorWrites[0].dstBinding = 0;
            descriptorWrites[0].dstArrayElement = 0;
            descriptorWrites[0].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
            descriptorWrites[0].descriptorCount = 1;
            descriptorWrites[0].pBufferInfo = &bufferInfo;

            VkDescriptorBufferInfo storageBufferInfoLastFrame{};
            storageBufferInfoLastFrame.buffer = shaderStorageBuffers[i];
            storageBufferInfoLastFrame.offset = 0;
            storageBufferInfoLastFrame.range = sizeof(GPUMeshData) * numMeshes;
            descriptorWrites[1].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
            descriptorWrites[1].dstSet = descriptorSets[i];
            descriptorWrites[1].dstBinding = 1;
            descriptorWrites[1].dstArrayElement = 0;
            descriptorWrites[1].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
            descriptorWrites[1].descriptorCount = 1;
            descriptorWrites[1].pBufferInfo = &storageBufferInfoLastFrame;

            VkDescriptorImageInfo imageInfo{};
            imageInfo.imageLayout = imageLayout;
            imageInfo.imageView = textureImageView;
            imageInfo.sampler = textureSampler;
            descriptorWrites[2].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
            descriptorWrites[2].dstSet = descriptorSets[i];
            descriptorWrites[2].dstBinding = 2;
            descriptorWrites[2].dstArrayElement = 0;
            descriptorWrites[2].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
            descriptorWrites[2].descriptorCount = 1;
            descriptorWrites[2].pImageInfo = &imageInfo;

            vkUpdateDescriptorSets(device, static_cast<uint32_t>(descriptorWrites.size()), descriptorWrites.data(), 0, nullptr);
        }
    }

    void createVertexBuffer(std::vector<VertexShaderData> vertices, VkDevice device, VkBuffer& vertexBuffer, VkDeviceMemory& vertexBufferMemory, VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties)
    {
        VkDeviceSize bufferSize = sizeof(vertices[0]) * vertices.size();

        VkBuffer stagingBuffer;
        VkDeviceMemory stagingBufferMemory;
        createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
        
        void* data;
        vkMapMemory(device, stagingBufferMemory, 0, bufferSize, 0, &data);
            memcpy(data, vertices.data(), (size_t) bufferSize);
        vkUnmapMemory(device, stagingBufferMemory);

        createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, vertexBuffer, vertexBufferMemory, memProperties);

        copyBuffer(stagingBuffer, vertexBuffer, bufferSize, queue, device, pool);

        vkDestroyBuffer(device, stagingBuffer, nullptr);
        vkFreeMemory(device, stagingBufferMemory, nullptr);

         m_vertexBuffers.push_back(vertexBuffer);
    }

    void createIndexBuffer(std::vector<uint16_t> indices, VkDevice device, VkBuffer& indexBuffer, VkDeviceMemory& indexBufferMemory, VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties) 
    {
        VkDeviceSize bufferSize = sizeof(indices[0]) * indices.size();
        VkBuffer stagingBuffer;
        VkDeviceMemory stagingBufferMemory;
        createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
        void* data;
        vkMapMemory(device, stagingBufferMemory, 0, bufferSize, 0, &data);
            memcpy(data, indices.data(), (size_t) bufferSize);
        vkUnmapMemory(device, stagingBufferMemory);
        createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_INDEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, indexBuffer, indexBufferMemory, memProperties);
        copyBuffer(stagingBuffer, indexBuffer, bufferSize, queue, device, pool);
        vkDestroyBuffer(device, stagingBuffer, nullptr);
        vkFreeMemory(device, stagingBufferMemory, nullptr);
        m_indexBuffer = indexBuffer;
    }

    void createUniformBuffers(std::vector<VkBuffer>& uniformBuffers, std::vector<VkDeviceMemory>& uniformBuffersMemory, std::vector<void*>& uniformBuffersMapped, VkDevice device, VkPhysicalDeviceMemoryProperties memProperties) 
    {
        VkDeviceSize bufferSize = sizeof(GPUCamera);
        uniformBuffers.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        uniformBuffersMemory.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        uniformBuffersMapped.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        for (size_t i = 0; i < ogun::constants::MAX_FRAMES_IN_FLIGHT; i++) 
        {
            createBuffer(device, bufferSize, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, uniformBuffers[i], uniformBuffersMemory[i], memProperties);
            vkMapMemory(device, uniformBuffersMemory[i], 0, bufferSize, 0, &uniformBuffersMapped[i]);
        }
    }

    void createStorageBuffers(VkDevice device, VkPhysicalDeviceMemoryProperties memProperties, std::vector<GPUMeshData> meshes, std::vector<VkBuffer>& shaderStorageBuffers,
                              std::vector<VkDeviceMemory>& shaderStorageBuffersMemory, VkQueue& queue, VkCommandPool& pool)
    {
        VkDeviceSize bufferSize = sizeof(GPUMeshData) * ogun::constants::MAX_MESH_COUNT;

        // Create a staging buffer used to upload data to the gpu
        VkBuffer stagingBuffer;
        VkDeviceMemory stagingBufferMemory;
        createBuffer(device, bufferSize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, memProperties);
        
        void* data;
        vkMapMemory(device, stagingBufferMemory, 0, bufferSize, 0, &data);
            memcpy(data, meshes.data(), (size_t)bufferSize);
        vkUnmapMemory(device, stagingBufferMemory);

        shaderStorageBuffers.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        shaderStorageBuffersMemory.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        // Copy initial particle data to all storage buffers
        for (size_t i = 0; i < ogun::constants::MAX_FRAMES_IN_FLIGHT; i++) {
            createBuffer(device, bufferSize, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, shaderStorageBuffers[i], shaderStorageBuffersMemory[i], memProperties);
            copyBuffer(stagingBuffer, shaderStorageBuffers[i], bufferSize, queue, device, pool);
        }

        vkDestroyBuffer(device, stagingBuffer, nullptr);
        vkFreeMemory(device, stagingBufferMemory, nullptr);
    }

private:

};

}; // namespace ogun