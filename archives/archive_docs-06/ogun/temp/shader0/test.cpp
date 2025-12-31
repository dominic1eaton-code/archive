




    void createDescriptorSetLayout(VkDevice m_device, VkDescriptorSetLayout m_descriptorSetLayout)
    {
        VObject<int> obj;
        VkDescriptorSetLayoutBinding cameraBinding{};
        cameraBinding.binding = 0;
        cameraBinding.descriptorCount = 1;
        cameraBinding.descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        cameraBinding.pImmutableSamplers = nullptr;
        cameraBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;
        // cameraBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT | VK_SHADER_STAGE_FRAGMENT_BIT;

        VkDescriptorSetLayoutBinding meshBinding{};
        meshBinding.binding = 1;
        meshBinding.descriptorCount = 1;
        meshBinding.descriptorType = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
        meshBinding.pImmutableSamplers = nullptr;
        meshBinding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;

        VkDescriptorSetLayoutBinding textureBinding{};
        textureBinding.binding = 1;
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
                                            &m_descriptorSetLayout));
    }

    
    
void createSSBO()
{
    std::vector<GPULight> pointlights[2];
    // pointlights[0].position = glm::vec3(2.0f,2.0f,2.0f);
    // pointlights[0].ambient =  glm::vec3(1.0f,0,0);
    // pointlights[0].diffuse = glm::vec3(0,0,0);
    // pointlights[0].specular = glm::vec3(0,0,0);
    // pointlights[0].k0 = 1.0f;
    // pointlights[0].k1 = 0.09f;
    // pointlights[0].k2 = 0.032f;
    
    // pointlights[1].position = glm::vec3(-4.0f,4.0f,2.0f);
    // pointlights[1].ambient =  glm::vec3(1.0f,0,0);
    // pointlights[1].diffuse = glm::vec3(0,0,0);
    // pointlights[1].specular = glm::vec3(0,0,0);
    // pointlights[1].k0 = 1.0f;
    // pointlights[1].k1 = 0.09f;
    // pointlights[1].k2 = 0.032f;

    // std::vector<GPULight> dirlights[1];
    // dirlights[0].direction = glm::vec3(2.0f,2.0f,2.0f);
    // dirlights[0].ambient =  glm::vec3(1.0f,0,0);
    // dirlights[0].diffuse = glm::vec3(0,0,0);
    // dirlights[0].specular = glm::vec3(0,0,0);

    // std::vector<GPULight> spotlights[1];
    // spotlights[1].position = glm::vec3(-4.0f,4.0f,2.0f);
    // spotlights[1].ambient =  glm::vec3(1.0f,0,0);
    // spotlights[1].diffuse = glm::vec3(0,0,0);
    // spotlights[1].specular = glm::vec3(0,0,0);
    // spotlights[1].k0 = 1.0f;
    // spotlights[1].k1 = 0.09f;
    // spotlights[1].k2 = 0.032f;
    // spotlights[1].c0 = glm::cos(glm::radians(12.5f));
    // spotlights[1].c1 = glm::cos(glm::radians(15.0f));

};








const uint32_t NUM_LIGHTS = 4;

struct GPUMesh
{
    alignas(16) glm::mat4 model;
};

struct GPULight
{
    // int type;
    alignas(4) float posX;
    alignas(4) float posY;
    alignas(4) float posZ;
    alignas(16) glm::vec4 ambient;
    alignas(16) glm::vec4 diffuse;
    alignas(16) glm::vec4 specular;
};

struct Vertex
{
    glm::vec3 position;
    glm::vec3 color;
};

class Mesh
{
public:
    Mesh() = default;
    // Mesh(glm::vec3 position, glm::vec3 color, float scale);
    virtual ~Mesh(void);

    /* */
    // virtual const std::vector<Vertex> vertices();

    /* */
    virtual const std::vector<uint16_t> indices();

    /* */
    virtual bool indexed();

    /* */
    glm::vec3 position();
    
    /* */
    glm::vec3 color();
    
    /* */
    glm::vec3 normal();
    
    /* */
    float scale();
    
    /* */
    glm::vec3 size();

protected:
    /* */
    virtual void computeVertices() = 0;

    /* */
    virtual void updateIndices() = 0;

    /* */
    virtual void resize(glm::vec3 size);

    /* */
    virtual void rescale(float scale);

    /* */
    virtual void reposition(glm::vec3 position);

    /* */
    virtual void changeColor(glm::vec3 color);

    /* */
    bool m_indexed;

    /* */
    // std::vector<GPUVertex> m_vertices;

    /* */
    std::vector<uint16_t> m_indices;

    /* */
    glm::vec3 m_position;

    /* */
    glm::vec3 m_color;

    /* */
    glm::vec3 m_normal;

    /* */
    // glm::vec3 m_normal;

    /* */
    float m_scale;

    /* */
    glm::vec3 m_size;
};

// Mesh::Mesh()
//     : m_position({0.0f, 0.0f, 0.0f})
//     , m_color({1.0f, 1.0f, 1.0f})
//     , m_scale(0.3f)
//     , m_size(1.0f)
// {}

// Mesh::Mesh(glm::vec3 position, glm::vec3 color, float scale)
//     : m_position(position)
//     , m_color(color)
//     , m_scale(scale)
//     , m_size(1.0f)
// {}

Mesh::~Mesh()
{}

glm::vec3 Mesh::position()
{
    return m_position;
}

glm::vec3 Mesh::color()
{
    return m_color;
}

glm::vec3 Mesh::normal()
{
    return m_normal;
}

float Mesh::scale()
{
    return m_scale;
}

glm::vec3 Mesh::size()
{
    return m_size;
}

// const std::vector<Vertex> Mesh::vertices()
// {
//     return m_vertices;
// }

const std::vector<uint16_t> Mesh::indices()
{
    return m_indices;
}

void Mesh::computeVertices()
{}

bool Mesh::indexed()
{
    m_indexed = !indices().empty();
    return m_indexed;
}

void Mesh::rescale(float scale)
{
    m_scale = scale;
}

void Mesh::reposition(glm::vec3 position)
{
    m_position = position;
}

void Mesh::changeColor(glm::vec3 color)
{
    m_color = color;
}

void Mesh::resize(glm::vec3 size)
{
    m_size = size;
}


class Triangle : virtual public Mesh
{
public:
    Triangle();
    Triangle(glm::vec3 position, float scale, glm::vec3 color);
    virtual ~Triangle(void);

protected:
    /* */
    // void computeVertices() override;

    /* */
    void updateIndices() override;
};


Triangle::Triangle()
{
    // computeVertices();
}

Triangle::Triangle(glm::vec3 position, float scale, glm::vec3 color)
    // : Mesh(position, color, scale)
{
    // computeVertices();
}

Triangle::~Triangle()
{}

// void Triangle::computeVertices()
// {
//     m_vertices = {
//         {{m_position[0]               , m_position[1] - m_scale/2.0f, m_position[2]}, m_color},
//         {{m_position[0] + m_scale/2.0f, m_position[1] + m_scale/2.0f, m_position[2]}, m_color},
//         {{m_position[0] - m_scale/2.0f, m_position[1] + m_scale/2.0f, m_position[2]}, m_color}
//     };
// }

void Triangle::updateIndices()
{}


/**
 * 1 - 2
 * | \ |              y
 * 0 - 3              ^
 * tri0: 0 - 1 - 3    | 
 * tri1: 1 - 2 - 3    o --> x
 */
struct Square
{
    Square()
        : Square({0.0f, 0.0f, 0.0f})
    {}

    Square(glm::vec3 o)
        : origin(o)
        , scale(1.0f, 1.0f, 1.0f)
    {
        points.resize(4);
        computePoints();
        computeVertices();
        computeIndices();
    }

    ~Square()
    {}

    inline std::vector<float> vertices() const { return verts; }

    inline std::vector<float> indices() const { return inds; }
    
    void computePoints()
    {
        points[0] = glm::vec3(origin.x - scale.x/2.0f, origin.y - scale.y/2.0f, origin.z);
        points[1] = glm::vec3(origin.x - scale.x/2.0f, origin.y + scale.y/2.0f, origin.z);
        points[2] = glm::vec3(origin.x + scale.x/2.0f, origin.y + scale.y/2.0f, origin.z);
        points[3] = glm::vec3(origin.x + scale.x/2.0f, origin.y - scale.y/2.0f, origin.z);
    }

    void computeVertices()
    {
        // verts = {
        //     {points[0], color[0], texture[0]},
        //     {points[1], color[1], texture[1]},
        //     {points[2], color[2], texture[2]},
        //     {points[3], color[3], texture[3]}
        // };
    }

    void computeIndices()
    {

    }

    std::vector<glm::vec3> points;
    glm::vec3 scale;
    glm::vec3 origin;
    glm::mat4 rotation;
    std::vector<float> verts;
    std::vector<float> inds;

};





void loadScene(std::vector<float>& vertices, std::vector<float>& indices)
{
    // populate scene
    // std::vector<GPUCamera> cameras{};
    // std::vector<GPUMesh> meshes{};
    // std::vector<GPULight> lights{};

    // cameras.resize(1);
    // meshes.resize(1);
    // lights.resize(1);

    // cameras[0].model = glm::mat4(0);
    // cameras[0].view  = glm::mat4(0);
    // cameras[0].proj  = glm::mat4(0);

    // meshes[0].model = glm::mat4(0);

    // vertices.push_back(1.0f);
    // vertices.push_back(1.0f);
    // vertices.push_back(1.0f);
    // indices.push_back(1.0f);
    
    // lights[0].model = glm::mat4(0);

}










class TestShader0
{
public:
    TestShader0() = default;
    virtual ~TestShader0(void) = default;

    void update(uint32_t index, VkExtent2D extent, std::vector<void*> uniformBuffersMapped);

private:

    std::vector<std::string> vertexShaders;

    std::vector<std::string> fragmentShaders;

    std::vector<std::string> computeShaders;
    // std::vector<std::string> tesselationShaders; // terrain
    // std::vector<std::string> geometryShaders;

    struct Uniform0Data
    {
        alignas(16) glm::mat4 model;
        alignas(16) glm::mat4 view;
        alignas(16) glm::mat4 proj;
    };

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
    }

    void createIndexBuffer(std::vector<VertexShaderData> indices, VkDevice device, VkBuffer& indexBuffer, VkDeviceMemory& indexBufferMemory, VkQueue& queue, VkCommandPool& pool, VkPhysicalDeviceMemoryProperties memProperties) 
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
    }

    void createUniformBuffers(std::vector<VkBuffer>& uniformBuffers, std::vector<VkDeviceMemory>& uniformBuffersMemory, std::vector<void*>& uniformBuffersMapped, VkDevice device, VkPhysicalDeviceMemoryProperties memProperties) 
    {
        VkDeviceSize bufferSize = sizeof(Uniform0Data);
        uniformBuffers.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        uniformBuffersMemory.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        uniformBuffersMapped.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        for (size_t i = 0; i < ogun::constants::MAX_FRAMES_IN_FLIGHT; i++) 
        {
            createBuffer(device, bufferSize, VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT, VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT, uniformBuffers[i], uniformBuffersMemory[i], memProperties);
            vkMapMemory(device, uniformBuffersMemory[i], 0, bufferSize, 0, &uniformBuffersMapped[i]);
        }
    }
            
    void createDescriptorPool(VkDevice device, VkDescriptorPool& descriptorPool) 
    {
        std::array<VkDescriptorPoolSize, 2> poolSizes{};
        poolSizes[0].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
        poolSizes[0].descriptorCount = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);
        poolSizes[1].type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
        poolSizes[1].descriptorCount = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        VkDescriptorPoolCreateInfo poolInfo{};
        poolInfo.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
        poolInfo.poolSizeCount = static_cast<uint32_t>(poolSizes.size());
        poolInfo.pPoolSizes = poolSizes.data();
        poolInfo.maxSets = static_cast<uint32_t>(ogun::constants::MAX_FRAMES_IN_FLIGHT);

        if (vkCreateDescriptorPool(device, &poolInfo, nullptr, &descriptorPool) != VK_SUCCESS) {
            throw std::runtime_error("failed to create descriptor pool!");
        }
    }

    void createDescriptorSets(VkDevice device, std::vector<VkDescriptorSet>& descriptorSets, VkDescriptorSetLayout descriptorSetLayout, VkDescriptorPool descriptorPool,
                            std::vector<VkBuffer>& uniformBuffers, VkSampler textureSampler, VkImageView textureImageView, VkImageLayout imageLayout)
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
            VkDescriptorBufferInfo bufferInfo{};
            bufferInfo.buffer = uniformBuffers[i];
            bufferInfo.offset = 0;
            // bufferInfo.range = sizeof(GPUCamera);

            VkDescriptorImageInfo imageInfo{};
            imageInfo.imageLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
            imageInfo.imageView = textureImageView;
            imageInfo.sampler = textureSampler;

            std::array<VkWriteDescriptorSet, 2> descriptorWrites{};

            descriptorWrites[0].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
            descriptorWrites[0].dstSet = descriptorSets[i];
            descriptorWrites[0].dstBinding = 0;
            descriptorWrites[0].dstArrayElement = 0;
            descriptorWrites[0].descriptorType = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
            descriptorWrites[0].descriptorCount = 1;
            descriptorWrites[0].pBufferInfo = &bufferInfo;

            descriptorWrites[1].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
            descriptorWrites[1].dstSet = descriptorSets[i];
            descriptorWrites[1].dstBinding = 1;
            descriptorWrites[1].dstArrayElement = 0;
            descriptorWrites[1].descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
            descriptorWrites[1].descriptorCount = 1;
            descriptorWrites[1].pImageInfo = &imageInfo;

            vkUpdateDescriptorSets(device, static_cast<uint32_t>(descriptorWrites.size()), descriptorWrites.data(), 0, nullptr);
        }
    }

    void createDescriptorSetLayout(VkDevice m_device, VkDescriptorSetLayout m_descriptorSetLayout)
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
        textureBinding.binding = 1;
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
                                            &m_descriptorSetLayout));
    }
};

void TestShader0::update(uint32_t index, VkExtent2D extent, std::vector<void*> uniformBuffersMapped)
{
    static auto startTime = std::chrono::high_resolution_clock::now();

    auto currentTime = std::chrono::high_resolution_clock::now();
    float time = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();

    Uniform0Data ubo{};
    ubo.model = glm::rotate(glm::mat4(1.0f), time * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    ubo.view = glm::lookAt(glm::vec3(2.0f, 2.0f, 2.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    ubo.proj = glm::perspective(glm::radians(45.0f), extent.width / (float) extent.height, 0.1f, 10.0f);
    ubo.proj[1][1] *= -1;

    memcpy(uniformBuffersMapped[index], &ubo, sizeof(ubo));
}



class VShader
{
public:
    VShader() = default;
    virtual ~VShader(void) = default;

private:
    ShaderType type;

    std::string name;

    std::string path;
};






    VDescriptorLayout descriptorLayout;
    descriptorLayout.device(m_device)
              .build();
    m_layout = descriptorLayout.layout();





    