/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_shader.h"
#include "vulkan_model.h"

using namespace ogun;


TestShader0::TestShader0()
    : m_modelMatrix(1.0f)
{}

void TestShader0::load(std::vector<VertexShaderData> vertices, std::vector<uint16_t> indices, std::vector<GPUMeshData> meshes, std::vector<GPUDirLight> dirlights,
            VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties, VkDevice device, VkExtent2D extent,
            VkDescriptorSetLayout& descriptorSetLayout, VkSampler textureSampler, VkImageView textureImageView, VkImageLayout imageLayout,
            std::string shaderPath)
{
    m_extent = extent;
    m_device = device;
    m_memProperties = memProperties;
    m_queue = queue;
    m_pool = pool;

    // shader files 
     std::vector<std::filesystem::path> shaderFiles;
    shaderFiles.push_back(std::filesystem::path(shaderPath) / "lighting" / "default_lighting.vert.spv");
    // shaderFiles.push_back(std::filesystem::path(shaderPath) / "lighting" / "default_lighting.geom.spv");
    shaderFiles.push_back(std::filesystem::path(shaderPath) / "lighting" / "default_lighting.frag.spv");
    shaderFiles.push_back(std::filesystem::path(shaderPath) / "lighting" / "default_lighting.comp.spv");

    VShader shader;
    shader.name(shaderFiles[0].string())
        .stage(VK_SHADER_STAGE_VERTEX_BIT)
        .device(m_device)
        .build();
    m_shaders.push_back(shader);
    
    // VShader shader2;
    // shader2.name(shaderFiles[1].string())
    //     .stage(VK_SHADER_STAGE_GEOMETRY_BIT)
    //     .device(m_device)
    //     .build();
    // m_shaders.push_back(shader2);

    VShader shader0;
    shader0.name(shaderFiles[1].string())
        .stage(VK_SHADER_STAGE_FRAGMENT_BIT)
        .device(m_device)
        .build();
    m_shaders.push_back(shader0);

    // VShader shader1;
    // shader1.name(shaderFiles[2].string())
    //     .stage(VK_SHADER_STAGE_COMPUTE_BIT)
    //     .device(m_device)
    //     .build();
    //     m_shaders.push_back(shader1);

    // shader data buffers
    m_gpuVertexBuffers.resize(1);
    createVertexBuffer(vertices, m_gpuVertexBuffers[0]);//, sizeof(vertices[0]) * vertices.size());
    createIndexBuffer(indices, m_gpuIndexBuffer);//, sizeof(indices[0]) * indices.size());
    createUniformBuffers(m_gpuCameraBuffers, sizeof(GPUCamera));
    createStorageBuffers(meshes, m_gpuMeshBuffers, sizeof(GPUMeshData) * meshes.size());
    createUniformBuffers(m_gpuViewBuffers, sizeof(GPUView));
    createUniformBuffers(m_cursorViewBuffers, sizeof(GPUCursor));
    // createStorageBuffers(dirlights, m_gpuDirLightBuffers, sizeof(GPUDirLight) * dirlights.size());
    // createUniformBuffers(m_gpuMaterialBuffers, sizeof(GPUMaterial));

    // shader descriptors
    createDescriptorSetLayout();
    createDescriptorPool();
    createDescriptorSets(textureSampler, textureImageView, imageLayout, meshes.size(), dirlights.size());

    for (auto gpuvertexbuffer : m_gpuVertexBuffers)
        m_vertexBuffers.push_back(gpuvertexbuffer.buffer);
    m_indexBuffer = m_gpuIndexBuffer.buffer;
    descriptorSetLayout = m_descriptorSetLayout;
}


void TestShader0::update(float tick, uint32_t currentImage, glm::mat4 view, glm::vec2 gcursor)
{
    GPUCamera camera;
    float aspect = 4.0f / 3.0f;

    // if (update)
    // {
        // update = false;
        // // float aspect = m_extent.width / (float) m_extent.height;
        // // camera.model = glm::rotate(glm::mat4(1.0f), tick * glm::radians(45.0f), glm::vec3(0.0f, 0.5f, 1.0f));
        // float rotatespeed = 0.5f;
        // float movespeed = 0.1;
        // glm::vec3 translation = glm::vec3(0.0 * movespeed) * axis;
        // // float rotation = glm::radians(angle * rotatespeed);
        // float rotation = glm::radians(angle * rotatespeed);
        // glm::mat4 rotationMatrix = glm::rotate(m_modelMatrix, rotation, axis);
        // std::cout << angle << std::endl;
        // m_modelMatrix = glm::translate(rotationMatrix, translation);
    // }
    // camera.view = glm::lookAt(glm::vec3(8.0f, 8.0f, 8.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    camera.model = m_modelMatrix;
    camera.view = view;
    camera.proj = glm::perspective(glm::radians(45.0f), aspect, 0.1f, 100.0f);
    // camera.model = glm::mat4(1.0f);
    // camera.view = glm::translate(glm::mat4(1.0f), glm::vec3(0.0f, 0.0f, -8.0f));
    // camera.proj = glm::perspective(glm::radians(45.0f), aspect, 0.1f, 100.0f);
    camera.proj[1][1] *= -1;
    memcpy(m_gpuCameraBuffers[currentImage].data, &camera, sizeof(camera));

    GPUView gview;
    gview.position = glm::vec4(gcursor.x, gcursor.y, 4.0f, 1.0f);
    memcpy(m_gpuViewBuffers[currentImage].data, &gview, sizeof(gview));

    GPUCursor cursor;
    // cursor.position = gcursor;
    cursor.position = glm::vec4(2.0f, 0.0f, 0.0f, 0.0f);
    memcpy(m_cursorViewBuffers[currentImage].data, &cursor, sizeof(cursor));
}

void TestShader0::updateStorageBuffer()
{

}

template<typename T>
void updateBuffer(std::vector<T> udata, VBuffer& vbuffer, VkDeviceSize dataIndex)
{}

void TestShader0::updateVertexBuffer(std::vector<VertexShaderData> udata, VkDeviceSize dataIndex)
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

void TestShader0::createVertexBuffer(std::vector<VertexShaderData> vertices, VBuffer& vbuffer)//, VkDeviceSize buffersize)
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

void TestShader0::createIndexBuffer(std::vector<uint16_t> indices, VBuffer& vbuffer)//, VkDeviceSize buffersize) 
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

void TestShader0::createUniformBuffers(std::vector<VBuffer>& vbuffer, VkDeviceSize buffersize) 
{
    // VkDeviceSize bufferSize = sizeof(GPUCamera);
    vbuffer.resize(m_buffersetSize);
    for (size_t i = 0; i < m_buffersetSize; i++) 
    {
        VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, vbuffer[i].buffer, vbuffer[i].memory, m_memProperties);
        vkMapMemory(m_device, vbuffer[i].memory, 0, buffersize, 0, &vbuffer[i].data);
    }
}

template<typename T>
void TestShader0::createStorageBuffers(std::vector<T> vdata, std::vector<VBuffer>& vbuffer, VkDeviceSize buffersize)
{
    // VkDeviceSize bufferSize = sizeof(GPUMeshData) * ogun::constants::MAX_MESH_COUNT;
    // Create a staging buffer used to upload data to the gpu
    VkBuffer stagingBuffer;
    VkDeviceMemory stagingBufferMemory;
    VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_TRANSFER_SRC_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, stagingBuffer, stagingBufferMemory, m_memProperties);
    void* data;
    vkMapMemory(m_device, stagingBufferMemory, 0, buffersize, 0, &data);
        memcpy(data, vdata.data(), (size_t)buffersize);
    vkUnmapMemory(m_device, stagingBufferMemory);
    vbuffer.resize(m_buffersetSize);
    // Copy initial particle data to all storage buffers
    for (size_t i = 0; i < m_buffersetSize; i++) 
    {
        VulkanModelSupport::createBuffer(m_device, buffersize, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT, VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT, vbuffer[i].buffer, vbuffer[i].memory, m_memProperties);
        VulkanModelSupport::copyBuffer(stagingBuffer, vbuffer[i].buffer, buffersize, m_queue, m_device, m_pool);
    }
    vkDestroyBuffer(m_device, stagingBuffer, nullptr);
    vkFreeMemory(m_device, stagingBufferMemory, nullptr);
}

void TestShader0::createDescriptorPool()
{
    std::array<VkDescriptorPoolSize, 5> poolSizes{};
    poolSizes[0].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    poolSizes[0].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    poolSizes[1].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    poolSizes[1].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    poolSizes[2].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
    poolSizes[2].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    poolSizes[3].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    poolSizes[3].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    poolSizes[4].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    poolSizes[4].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    // poolSizes[4].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    // poolSizes[4].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    // poolSizes[5].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    // poolSizes[5].descriptorCount = static_cast<uint32_t>(m_buffersetSize);

    VkDescriptorPoolCreateInfo poolInfo{};
    poolInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
    poolInfo.poolSizeCount = static_cast<uint32_t>(poolSizes.size());
    poolInfo.pPoolSizes = poolSizes.data();
    poolInfo.maxSets = static_cast<uint32_t>(m_buffersetSize);
    if (vkCreateDescriptorPool(m_device, &poolInfo, nullptr, &m_descriptorPool) != VK_SUCCESS)
    {
        throw std::runtime_error("failed to create descriptor m_pool!");
    }
}

void TestShader0::createDescriptorSetLayout()
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

    VkDescriptorSetLayoutBinding viewBinding{};
    viewBinding.binding = 3;
    viewBinding.descriptorCount = 1;
    viewBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    viewBinding.pImmutableSamplers = nullptr;
    viewBinding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    VkDescriptorSetLayoutBinding cursorBinding{};
    cursorBinding.binding = 4;
    cursorBinding.descriptorCount = 1;
    cursorBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    cursorBinding.pImmutableSamplers = nullptr;
    cursorBinding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    // VkDescriptorSetLayoutBinding lightBinding{};
    // lightBinding.binding = 4;
    // lightBinding.descriptorCount = 1;
    // lightBinding.descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    // lightBinding.pImmutableSamplers = nullptr;
    // lightBinding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    // VkDescriptorSetLayoutBinding materialBinding{};
    // materialBinding.binding = 5;
    // materialBinding.descriptorCount = 1;
    // materialBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    // materialBinding.pImmutableSamplers = nullptr;
    // materialBinding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    std::vector<VkDescriptorSetLayoutBinding> uboLayoutBindings;
    uboLayoutBindings.push_back(cameraBinding);
    uboLayoutBindings.push_back(meshBinding);
    uboLayoutBindings.push_back(textureBinding);
    uboLayoutBindings.push_back(viewBinding);
    uboLayoutBindings.push_back(cursorBinding);
    // uboLayoutBindings.push_back(lightBinding);
    // uboLayoutBindings.push_back(materialBinding);

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
                                            &m_descriptorSetLayout));
}

void TestShader0::createDescriptorSets(VkSampler textureSampler, VkImageView textureImageView, VkImageLayout imageLayout,
                            uint32_t numMeshes, uint32_t numDirLights)
{
    VObject<int> obj;
    std::vector<VkDescriptorSetLayout> layouts(m_buffersetSize, m_descriptorSetLayout);
    VkDescriptorSetAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    allocInfo.descriptorPool = m_descriptorPool;
    allocInfo.descriptorSetCount = static_cast<uint32_t>(m_buffersetSize);
    allocInfo.pSetLayouts = layouts.data();

    m_descriptorSets.resize(m_buffersetSize);
    obj.createvk(vkAllocateDescriptorSets(m_device,
                                    &allocInfo,
                                    m_descriptorSets.data()));

    for (size_t i = 0; i < m_buffersetSize; i++) 
    {
        std::array<VkWriteDescriptorSet, 5> descriptorWrites{};

        VkDescriptorBufferInfo cameraBufferInfo{};
        cameraBufferInfo.buffer = m_gpuCameraBuffers[i].buffer;
        cameraBufferInfo.offset = 0;
        cameraBufferInfo.range = sizeof(GPUCamera);
        descriptorWrites[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[0].dstSet = m_descriptorSets[i];
        descriptorWrites[0].dstBinding = 0;
        descriptorWrites[0].dstArrayElement = 0;
        descriptorWrites[0].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        descriptorWrites[0].descriptorCount = 1;
        descriptorWrites[0].pBufferInfo = &cameraBufferInfo;

        VkDescriptorBufferInfo meshBufferInfo{};
        meshBufferInfo.buffer = m_gpuMeshBuffers[i].buffer;
        meshBufferInfo.offset = 0;
        meshBufferInfo.range = sizeof(GPUMeshData) * numMeshes;
        descriptorWrites[1].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[1].dstSet = m_descriptorSets[i];
        descriptorWrites[1].dstBinding = 1;
        descriptorWrites[1].dstArrayElement = 0;
        descriptorWrites[1].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        descriptorWrites[1].descriptorCount = 1;
        descriptorWrites[1].pBufferInfo = &meshBufferInfo;

        VkDescriptorImageInfo imageInfo{};
        imageInfo.imageLayout = imageLayout;
        imageInfo.imageView = textureImageView;
        imageInfo.sampler = textureSampler;
        descriptorWrites[2].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[2].dstSet = m_descriptorSets[i];
        descriptorWrites[2].dstBinding = 2;
        descriptorWrites[2].dstArrayElement = 0;
        descriptorWrites[2].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
        descriptorWrites[2].descriptorCount = 1;
        descriptorWrites[2].pImageInfo = &imageInfo;

        VkDescriptorBufferInfo viewUniformBufferInfo{};
        viewUniformBufferInfo.buffer = m_gpuViewBuffers[i].buffer;
        viewUniformBufferInfo.offset = 0;
        viewUniformBufferInfo.range = sizeof(GPUView);
        descriptorWrites[3].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[3].dstSet = m_descriptorSets[i];
        descriptorWrites[3].dstBinding = 3;
        descriptorWrites[3].dstArrayElement = 0;
        descriptorWrites[3].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        descriptorWrites[3].descriptorCount = 1;
        descriptorWrites[3].pBufferInfo = &viewUniformBufferInfo;

        VkDescriptorBufferInfo cursorUniformBufferInfo{};
        cursorUniformBufferInfo.buffer = m_cursorViewBuffers[i].buffer;
        cursorUniformBufferInfo.offset = 0;
        viewUniformBufferInfo.range = sizeof(GPUCursor);
        descriptorWrites[4].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        descriptorWrites[4].dstSet = m_descriptorSets[i];
        descriptorWrites[4].dstBinding = 4;
        descriptorWrites[4].dstArrayElement = 0;
        descriptorWrites[4].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        descriptorWrites[4].descriptorCount = 1;
        descriptorWrites[4].pBufferInfo = &cursorUniformBufferInfo;

        // VkDescriptorBufferInfo lighStorageBufferInfo{};
        // lighStorageBufferInfo.buffer = m_gpuDirLightBuffers[i].buffer;
        // lighStorageBufferInfo.offset = 0;
        // lighStorageBufferInfo.range = sizeof(GPUDirLight) * numDirLights;
        // descriptorWrites[4].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        // descriptorWrites[4].dstSet = m_descriptorSets[i];
        // descriptorWrites[4].dstBinding = 4;
        // descriptorWrites[4].dstArrayElement = 0;
        // descriptorWrites[4].descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        // descriptorWrites[4].descriptorCount = 1;
        // descriptorWrites[4].pBufferInfo = &lighStorageBufferInfo;

        // VkDescriptorBufferInfo materialUnifromBufferInfo{};
        // materialUnifromBufferInfo.buffer = m_gpuMaterialBuffers[i].buffer;
        // materialUnifromBufferInfo.offset = 0;
        // materialUnifromBufferInfo.range = sizeof(GPUMaterial);
        // descriptorWrites[5].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        // descriptorWrites[5].dstSet = m_descriptorSets[i];
        // descriptorWrites[5].dstBinding = 5;
        // descriptorWrites[5].dstArrayElement = 0;
        // descriptorWrites[5].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        // descriptorWrites[5].descriptorCount = 1;
        // descriptorWrites[5].pBufferInfo = &materialUnifromBufferInfo;

        vkUpdateDescriptorSets(m_device, static_cast<uint32_t>(descriptorWrites.size()), descriptorWrites.data(), 0, nullptr);
    }
}