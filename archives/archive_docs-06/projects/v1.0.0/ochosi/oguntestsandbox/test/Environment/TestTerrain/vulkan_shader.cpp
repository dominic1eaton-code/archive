/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_shader.h"
#include "vulkan_model.h"
#include "vulkan_terrain.h"

namespace ogun
{

void TerrainShader::init(VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties, VkDevice device,
                         std::string shaderPath)
{
    m_device = device;
    m_memProperties = memProperties;
    m_queue = queue;
    m_pool = pool;
    m_shaderPath = shaderPath;
}


void TerrainShader::update(float tick, uint32_t currentImage, glm::mat4 view)
{
    GPUCamera2 camera2;
    float aspect = 4.0f / 3.0f;
    camera2.model = glm::mat4(1.0f);
    camera2.view = view;
    memcpy(m_gpuCamera2Buffers[currentImage].data, &camera2, sizeof(camera2));

    GPUCamera camera;
    camera.model = glm::mat4(1.0f);
    camera.view = view;
    camera.proj = glm::perspective(glm::radians(45.0f), aspect, 0.1f, 1000.0f);
    camera.proj[1][1] *= -1;
    memcpy(m_gpuCameraBuffers[currentImage].data, &camera, sizeof(camera));
    
}


// template<typename T>
// void TerrainShader::update(std::vector<T> udata, VBuffer& vbuffer, VkDeviceSize dataIndex)
// {
// }

void TerrainShader::load(std::vector<TVertex> vertices, std::vector<uint16_t> indices,
                         size_t camerasize, Texture terrainHeightMap)
{
    /* create shader modules */
    createShaderModules();

    /* create shader buffers */
    // createBuffers();
    // uint8_t staging_multipier = 2;
    // size_t m_staging_size = staging_multipier * (vertices.size() + indices.size() + camerasize);
    // stagebuffer.create(m_staging_size);
    // vertexbuffer.create(vertices.size());
    // indexbuffer.create(indices.size());
    // uniformBuffer.create(camerasize);
    // vertexbuffer.copy(stagebuffer, vertices);
    // indexbuffer.copy(stagebuffer, indices);
    m_gpuVertexBuffers.resize(1);
    createVertexBuffer(vertices, m_gpuVertexBuffers[0]);//, sizeof(vertices[0]) * vertices.size());
    createIndexBuffer(indices, m_gpuIndexBuffer);//, sizeof(indices[0]) * indices.size());
    createUniformBuffers(m_gpuCamera2Buffers, sizeof(GPUCamera2));
    createUniformBuffers(m_gpuCameraBuffers, sizeof(GPUCamera));

    /* create shader descriptors */
    createDescriptors(terrainHeightMap);

    /* output */
    for (auto gpuvertexbuffer : m_gpuVertexBuffers)
        m_vertexBuffers.push_back(gpuvertexbuffer.buffer);
    m_indexBuffer = m_gpuIndexBuffer.buffer;
    // descriptorSetLayout = m_descriptorSetLayout;
}


void TerrainShader::updateVertexBuffer(std::vector<TVertex> udata, VkDeviceSize dataIndex)
{
   VBuffer sbuffer;
   VkDeviceSize buffersize = sizeof(udata[0]) * udata.size();
   VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, sbuffer.buffer, sbuffer.memory, m_memProperties);
   vkMapMemory(m_device, sbuffer.memory, 0, buffersize, 0, &sbuffer.data);
       memcpy(sbuffer.data, udata.data(), (size_t) buffersize);
   vkUnmapMemory(m_device, sbuffer.memory); // @todo use common storage buffer that unmaps minimal number of times (i.e at end of use of vertex/index/storage buffers)
   VulkanModelSupport::copyBuffer(sbuffer.buffer, m_gpuVertexBuffers[0].buffer, buffersize, m_queue, m_device, m_pool, 0, dataIndex);
   vkDestroyBuffer(m_device, sbuffer.buffer, nullptr);
   vkFreeMemory(m_device, sbuffer.memory, nullptr);
}

void TerrainShader::createVertexBuffer(std::vector<TVertex> vertices, VBuffer& vbuffer)//, VkDeviceSize buffersize)
{
    VkDeviceSize buffersize = sizeof(vertices[0]) * vertices.size();
    VBuffer sbuffer;
    // VkBuffer stagingBuffer;
    // VkDeviceMemory stagingBufferMemory;
    VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, sbuffer.buffer, sbuffer.memory, m_memProperties);
    VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, vbuffer.buffer, vbuffer.memory, m_memProperties);
    // void* data;
    vkMapMemory(m_device, sbuffer.memory, 0, buffersize, 0, &sbuffer.data);
        memcpy(sbuffer.data, vertices.data(), (size_t) buffersize);
    vkUnmapMemory(m_device, sbuffer.memory); // @todo use common storage buffer that unmaps minimal number of times (i.e at end of use of vertex/index/storage buffers)
    VulkanModelSupport::copyBuffer(sbuffer.buffer, vbuffer.buffer, buffersize, m_queue, m_device, m_pool);
    vkDestroyBuffer(m_device, sbuffer.buffer, nullptr);
    vkFreeMemory(m_device, sbuffer.memory, nullptr);
}

void TerrainShader::createIndexBuffer(std::vector<uint16_t> indices, VBuffer& vbuffer)//, VkDeviceSize buffersize) 
{
    VkDeviceSize buffersize = sizeof(indices[0]) * indices.size();
    VkBuffer stagingBuffer;
    VkDeviceMemory stagingBufferMemory;
    VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, m_memProperties);
    VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_INDEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, vbuffer.buffer, vbuffer.memory, m_memProperties);
    void* data;
    vkMapMemory(m_device, stagingBufferMemory, 0, buffersize, 0, &data);
        memcpy(data, indices.data(), (size_t) buffersize);
    vkUnmapMemory(m_device, stagingBufferMemory);
    VulkanModelSupport::copyBuffer(stagingBuffer, vbuffer.buffer, buffersize, m_queue, m_device, m_pool);
    vkDestroyBuffer(m_device, stagingBuffer, nullptr);
    vkFreeMemory(m_device, stagingBufferMemory, nullptr);
}

void TerrainShader::createUniformBuffers(std::vector<VBuffer>& vbuffer, VkDeviceSize buffersize) 
{
    // VkDeviceSize bufferSize = sizeof(GPUCamera);
    vbuffer.resize(m_buffersetSize);
    for (size_t i = 0; i < m_buffersetSize; i++) 
    {
        VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, vbuffer[i].buffer, vbuffer[i].memory, m_memProperties);
        vkMapMemory(m_device, vbuffer[i].memory, 0, buffersize, 0, &vbuffer[i].data);
    }
}

void TerrainShader::createShaderModules()
{
    std::string shader_class = "terrain";
    std::string shader_name = "terrain";
    // std::vector<std::string> shader_components_exts = {".vert", ".tesc", ".tese", ".frag"};
    // std::vector<VkShaderStageFlagBits> shader_components = {
    //     VK_SHADER_STAGE_VERTEX_BIT, VK_SHADER_STAGE_FRAGMENT_BIT, 
    //     VK_SHADER_STAGE_TESSELLATION_CONTROL_BIT, VK_SHADER_STAGE_TESSELLATION_EVALUATION_BIT};
    OShader s0;
    s0.name = shader_name;
    s0.type = shader_class;
    s0.ext = ".vert";
    s0.stage = VK_SHADER_STAGE_VERTEX_BIT;
    OShader s1;
    s1.name = shader_name;
    s1.type = shader_class;
    s1.ext = ".tesc";
    s1.stage = VK_SHADER_STAGE_TESSELLATION_CONTROL_BIT;
    OShader s2;
    s2.name = shader_name;
    s2.type = shader_class;
    s2.ext = ".tese";
    s2.stage = VK_SHADER_STAGE_TESSELLATION_EVALUATION_BIT;
    OShader s3;
    s3.name = shader_name;
    s3.type = shader_class;
    s3.ext = ".frag";
    s3.stage = VK_SHADER_STAGE_FRAGMENT_BIT;
    std::vector<OShader> ss;
    ss.push_back(s0);
    ss.push_back(s1);
    ss.push_back(s2);
    ss.push_back(s3);
    
    // shaderFiles.push_back(std::filesystem::path(shaderPath) / shader_class / shader_name);
    for (auto s : ss)
    {
        VShader shader;
        std::filesystem::path shader_file_path = std::filesystem::path(m_shaderPath) / s.type / (s.name + s.ext + ".spv");
        shader.name(shader_file_path.string())
            .stage(s.stage)
            .device(m_device)
            .build();
        m_shaders.push_back(shader);
    }
}

// template<typename T>
// void TerrainShader::createBuffers(std::vector<T> vdata, uint8_t setcount = 0)
// {
//     // createVertexBuffer(vertices);
//     // createIndexBuffer(indices);
//     // createUniformBuffer(cameraSize);

//     stagebuffer.create(m_staging_size);
//     vertexbuffer.create(verticessize);
//     indexbuffer.create(indicessize);
//     uniformBuffer.create(camerasize);

//     vertexbuffer.copy(stagebuffer, vertices);
//     indexbuffer.copy(stagebuffer, indices);
// }

void TerrainShader::createDescriptors(Texture texture)
{
    /* pool */
    VObject<int> obj;
    std::array<VkDescriptorPoolSize, 3> poolSizes{};
    poolSizes[0].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    poolSizes[0].descriptorCount = static_cast<uint32_t>(m_buffersetSize);
    
    poolSizes[1].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    poolSizes[1].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    poolSizes[2].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
    poolSizes[2].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    VkDescriptorPoolCreateInfo poolInfo{};
    poolInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
    poolInfo.poolSizeCount = static_cast<uint32_t>(poolSizes.size());
    poolInfo.pPoolSizes = poolSizes.data();
    poolInfo.maxSets = static_cast<uint32_t>(m_buffersetSize);
    
    // create vulkan object
    obj.createvk(vkCreateDescriptorPool(m_device,
                                        &poolInfo,
                                        nullptr,
                                        &m_descriptor.pool));

    /* layout */
    VkDescriptorSetLayoutBinding cameraBinding{};
    cameraBinding.binding = 0;
    cameraBinding.descriptorCount = 1;
    cameraBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    cameraBinding.pImmutableSamplers = nullptr;
    cameraBinding.stageFlags = VK_SHADER_STAGE_TESSELLATION_CONTROL_BIT;

    VkDescriptorSetLayoutBinding meshBinding{};
    meshBinding.binding = 1;
    meshBinding.descriptorCount = 1;
    meshBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    meshBinding.pImmutableSamplers = nullptr;
    meshBinding.stageFlags = VK_SHADER_STAGE_TESSELLATION_EVALUATION_BIT;

    VkDescriptorSetLayoutBinding textureBinding{};
    textureBinding.binding = 2;
    textureBinding.descriptorCount = 1;
    textureBinding.descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
    textureBinding.pImmutableSamplers = nullptr;
    textureBinding.stageFlags = VK_SHADER_STAGE_TESSELLATION_EVALUATION_BIT;

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
    obj.createvk(vkCreateDescriptorSetLayout(m_device,
                                            &layoutInfo,
                                            nullptr,
                                            &m_descriptor.layout));

    /* sets */
    std::vector<VkDescriptorSetLayout> layouts(m_buffersetSize, m_descriptor.layout);
    VkDescriptorSetAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    allocInfo.descriptorPool = m_descriptor.pool;
    allocInfo.descriptorSetCount = static_cast<uint32_t>(m_buffersetSize);
    allocInfo.pSetLayouts = layouts.data();

    m_descriptor.sets.resize(m_buffersetSize);
    obj.createvk(vkAllocateDescriptorSets(m_device,
                                    &allocInfo,
                                    m_descriptor.sets.data()));

    for (size_t i = 0; i < m_buffersetSize; i++) 
    {
        std::array<VkWriteDescriptorSet, 3> descriptorWrites{};
        VkDescriptorBufferInfo cameraBufferInfo{};
        
        VkDescriptorBufferInfo camera2BufferInfo{};
        size_t camera2buffersize = sizeof(GPUCamera2);
        camera2BufferInfo.buffer = m_gpuCamera2Buffers[i].buffer;
        camera2BufferInfo.offset = 0;
        camera2BufferInfo.range = camera2buffersize;
        descriptorWrites[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[0].dstSet = m_descriptor.sets[i];
        descriptorWrites[0].dstBinding = 0;
        descriptorWrites[0].dstArrayElement = 0;
        descriptorWrites[0].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        descriptorWrites[0].descriptorCount = 1;
        descriptorWrites[0].pBufferInfo = &camera2BufferInfo;
        
        size_t camerabuffersize = sizeof(GPUCamera);
        cameraBufferInfo.buffer = m_gpuCameraBuffers[i].buffer;
        cameraBufferInfo.offset = 0;
        cameraBufferInfo.range = camerabuffersize;
        descriptorWrites[1].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[1].dstSet = m_descriptor.sets[i];
        descriptorWrites[1].dstBinding = 1;
        descriptorWrites[1].dstArrayElement = 0;
        descriptorWrites[1].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        descriptorWrites[1].descriptorCount = 1;
        descriptorWrites[1].pBufferInfo = &cameraBufferInfo;

        VkDescriptorImageInfo imageInfo{};
        imageInfo.imageLayout = texture.layout;
        imageInfo.imageView = texture.view;
        imageInfo.sampler = texture.sampler;
        descriptorWrites[2].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[2].dstSet = m_descriptor.sets[i];
        descriptorWrites[2].dstBinding = 2;
        descriptorWrites[2].dstArrayElement = 0;
        descriptorWrites[2].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
        descriptorWrites[2].descriptorCount = 1;
        descriptorWrites[2].pImageInfo = &imageInfo;

        vkUpdateDescriptorSets(m_device, static_cast<uint32_t>(descriptorWrites.size()), descriptorWrites.data(), 0, nullptr);
    }
}

// void TerrainShader::createVertexBuffers(std::vector<TVertex> vertices)
// {
//     uint8_t sbufferIndex = 0;
//     VkDeviceSize buffersize = sizeof(vertices[0]) * vertices.size();
//     VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, vbuffer.buffer, vbuffer.memory, m_memProperties);
//     vkMapMemory(m_device, m_sbuffers[sbufferIndex].memory, 0, buffersize, 0, &m_sbuffers[sbufferIndex].data);
//     memcpy(sbuffer.data, vertices.data(), (size_t) buffersize);
//     vkUnmapMemory(m_device, sbuffer.memory);
//     VulkanModelSupport::copyBuffer(m_sbuffers[sbufferIndex].buffer, vbuffer.buffer, buffersize, m_queue, m_device, m_pool);
// }

// void TerrainShader::createIndexBuffer()
// {
// }

// void TerrainShader::createBindingBuffers()
// {
// }

};