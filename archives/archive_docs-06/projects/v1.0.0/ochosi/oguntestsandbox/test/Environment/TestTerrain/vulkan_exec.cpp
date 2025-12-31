
/**
 * @header
 * @copyright
 * @brief
 * @note 
 */

#include "vulkan_exec.h"
#include "vulkan_shader.h"

using namespace ogun;

VulkanModel::VulkanModel()
    : m_frameIndex(0)
    , m_move(0.0f)
    , m_angle(0.0f)
    , m_axis(glm::vec3(1.0f, 1.0f, 0.0f))
    , m_framebufferResized(false)
    , m_width(0u)
    , m_height(0u)
    , m_update(false)
    , m_cursorPosition(0.0f)
    , obj_transform(glm::vec3(0.0f))
    , bUpdateRecordCommands({})
{
    m_fences = new VFences();
    m_semaphores = new VSemaphores();
    m_shader = new TerrainShader();
    m_scene = new VScene();
    bUpdateRecordCommands.resize(ogun::constants::MAX_FRAMES_IN_FLIGHT);
    for (int i = 0; i < ogun::constants::MAX_FRAMES_IN_FLIGHT; i++)
        bUpdateRecordCommands[i] = false;
}

void VulkanModel::begin()
{

}

void VulkanModel::shutdown()
{
    // vkDeviceWaitIdle(device);
}

void VulkanModel::init(VulkanModelInfo info)
{
    std::string assetPath = "D:/dev/projects/oguntestsandbox/assets";
    std::string shaderLibraryPath = std::filesystem::path(std::filesystem::path(info.mount) / assetPath / "shaders").string();
    // std::string testTextureImage = std::filesystem::path(std::filesystem::path(info.mount) / "/dev/projects/v0.0.1/ogunv2/ogun/assets/textures/grass-texture-background.jpg").string();
    std::string testTextureImage = std::filesystem::path(std::filesystem::path(info.mount) / assetPath / "textures/wood.png").string();
    std::string testTerrainHeightMap = std::filesystem::path(std::filesystem::path(info.mount) / assetPath / "heightmaps/stl_heightmap1.png").string();

    /* core objects */
    VkApplicationInfo appInfo;
    appInfo.pNext = NULL;
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "TestOgunEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 1, 0);
    appInfo.pEngineName = "TestOgunEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 1, 0);
    appInfo.apiVersion = VK_MAKE_API_VERSION(0, 1, 1, 0);

    VInstance instance;
    instance.info(appInfo)
            .layers({"VK_LAYER_KHRONOS_validation"}) // @todo figure out path issue
            .extensions({"VK_KHR_surface", "VK_KHR_win32_surface", "VK_EXT_debug_utils"})
            .build();

    VkDebugUtilsMessengerEXT debugMessenger;
    bool enableValidation = true;
    VulkanModelSupport::setupDebugMessenger(true, instance.inst(), debugMessenger);

    VSurface surface;
    surface.hwnd(info.window.hwnd)
           .build(instance.inst());

    VPhysicalDevice pdevice;
    pdevice.select(instance.inst(), surface.surf());

    VLogicalDevice ldevice;
    ldevice.extensions({"VK_KHR_swapchain", "VK_KHR_shader_draw_parameters"})
           .device(pdevice.primary())
           .features(pdevice.info().features)
           .queueInfo(pdevice.queueInfo())
           .build(instance.inst());
    m_device = ldevice.primary();
    m_queues = ldevice.queues();

    VkExtent2D extent{info.window.width, info.window.height};
    VSwapchain swapchain;
    m_width = info.window.width;
    m_height = info.window.height;
    swapchain.device(m_device)
             .depth(pdevice.info().depthFormat)
             .surface(surface.surf())
             .extent(extent)
             .presentModes(pdevice.info().presentModes)
             .capabilities(pdevice.info().capabilities)
             .formats(pdevice.info().formats)
             .build(instance.inst(), pdevice.indices());
    m_swapchain = swapchain;

    VkSampleCountFlagBits msaaSamples = VK_SAMPLE_COUNT_1_BIT;
    VkPipelineBindPoint bindPoint = VK_PIPELINE_BIND_POINT_GRAPHICS;
    VRenderPass renderpass;
    renderpass.device(m_device)
              .format(swapchain.format())
              .depth(VulkanModelSupport::findDepthFormat(pdevice.primary()))
            //   .depth(pdevice.info().depthFormat)
              .bindpoint(bindPoint)
              .samples(pdevice.info().msaaSamples)
              .build();
    m_renderpass = renderpass.pass();

    m_fences->create("inflight", ogun::constants::MAX_FRAMES_IN_FLIGHT, VK_FENCE_CREATE_SIGNALED_BIT, m_device);
    m_semaphores->create("imageAvailable", ogun::constants::MAX_FRAMES_IN_FLIGHT, m_device);
    m_semaphores->create("renderFinished", ogun::constants::MAX_FRAMES_IN_FLIGHT, m_device);
    VkCommandPool commandPool = VulkanModelSupport::createCommandPool(m_device, pdevice.indices().graphics);
    m_commandBuffers = VulkanModelSupport::createCommandBuffers(m_device, commandPool);
    m_commandPool = commandPool;
    m_memProperties = pdevice.info().memoryProperties;

    /* resources */
    uint32_t mipLevels;
    VkSampler textureSampler;
    VulkanModelSupport::createTextureImage(pdevice.primary(), m_device, testTextureImage, ldevice.queues()[0], commandPool, pdevice.info().memoryProperties, m_textureImage, m_textureImageMemory, mipLevels);
    VulkanModelSupport::createTextureImageView(m_device, m_textureImage, mipLevels, m_textureImageView);
    VulkanModelSupport::createTextureSampler(pdevice.info().properties, m_device, textureSampler);
    
    terrainHeightMapImage.file = testTerrainHeightMap;
    terrainHeightMapImage.extent = VulkanModelSupport::createTextureImage(pdevice.primary(), m_device, terrainHeightMapImage.file , ldevice.queues()[0], commandPool, pdevice.info().memoryProperties, terrainHeightMapImage.image, terrainHeightMapImage.memory, terrainHeightMapImage.mipLevels);
    VulkanModelSupport::createTextureImageView(m_device, terrainHeightMapImage.image, terrainHeightMapImage.mipLevels, terrainHeightMapImage.view);
    VulkanModelSupport::createTextureSampler(pdevice.info().properties, m_device, terrainHeightMapImage.sampler);
    Texture textureheightmap;
    textureheightmap.format = VK_FORMAT_R8G8B8A8_SRGB;
    textureheightmap.layout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
    textureheightmap.sampler = terrainHeightMapImage.sampler;
    textureheightmap.view = terrainHeightMapImage.view;
    VulkanModelSupport::createColorResources(m_device, m_swapchain.format(), pdevice.info().msaaSamples, m_colorImage, m_colorImageMemory, m_swapchain.extent(), pdevice.info().memoryProperties, 1u, m_colorImageView);
    VulkanModelSupport::createDepthResources(m_device, pdevice.primary(), pdevice.info().msaaSamples, m_depthImage, m_depthImageMemory, m_swapchain.extent(), pdevice.info().memoryProperties, 1u, m_depthImageView);
    VulkanModelSupport::createFramebuffers(m_device, m_swapchain.extent(), m_renderpass, m_colorImageView, m_depthImageView, m_swapchain.imageViews(), m_framebuffers);

    /* scene data */
    std::vector<TVertex> vertices{};
    std::vector<uint16_t> indices{};
    std::vector<GPUMeshData> meshes{};
    std::vector<GPUDirLight> dirlights{};
    m_scene->load(vertices, indices, meshes, dirlights, terrainHeightMapImage.extent);
    m_indicesCount = indices.size();
    m_vertsCount = vertices.size();
    m_vertices = vertices;
    m_indices = indices;
    GPUCamera camera = m_scene->primaryCamera();

    /* pipeline(s) and shader(s) */
    // m_shader = new TestShader0();
    // m_shader->load(vertices, indices, meshes, dirlights,
    //                m_queues[0], commandPool, pdevice.info().memoryProperties, m_device, extent, //m_swapchain.extent(),
    //                m_descriptorSetLayout, textureSampler, m_textureImageView, VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL,
    //                shaderLibraryPath);
    m_shader = new TerrainShader();
    m_shader->init(m_queues[0], commandPool, pdevice.info().memoryProperties, m_device, shaderLibraryPath);
    m_shader->load(vertices, indices, sizeof(GPUCamera), textureheightmap);
    m_descriptorSetLayout = m_shader->layout();

    VGraphicsPipeline gpipeline;
    gpipeline.device(m_device)
             .pass(m_renderpass)
             .extent(swapchain.extent())
             .layout(m_descriptorSetLayout)
             .shaders(m_shader->shaders())
             .samples(pdevice.info().msaaSamples)
             .build();
    m_pipelines.push_back(gpipeline.pipeline());
    m_layout = gpipeline.pipelineLayout();
    m_deviceinfo = pdevice.info();
    m_pdevice = pdevice.primary();
    m_pindices = pdevice.indices();
    m_surface = surface.surf();
    m_instance = instance.inst();
    m_msaaSamples = pdevice.info().msaaSamples;
    m_shaders = m_shader->shaders();
};


void VulkanModel::move(float angle, glm::vec3 axis)
{
    // if (angle < 0) { m_move = 0; }
    m_update = true;
    m_move += angle;
    m_axis = axis;

    // if (angle > 0 && axis == glm::vec3(0.0f, 1.0f, 0.0f))
    // {
    //     cameraPos += cameraSpeed * cameraFront;
    // }
    // if (angle < 0 && axis == glm::vec3(0.0f, 1.0f, 0.0f))
    // {
    //     cameraPos -= cameraSpeed * cameraFront;
    // }
    // if (angle > 0 && axis == glm::vec3(1.0f, 0.0f, 0.0f))
    // {
    //     cameraPos -= glm::normalize(glm::cross(cameraFront, cameraUp)) * cameraSpeed;
    // }
    // if (angle < 0 && axis == glm::vec3(1.0f, 0.0f, 0.0f))
    // {
    //     cameraPos += glm::normalize(glm::cross(cameraFront, cameraUp)) * cameraSpeed;
    // }
}

void VulkanModel::transform(float angle, glm::vec3 axis, uint32_t type)
{
    std::cout << "camera AXIS: " << axis.x << " " << axis.y << " " << axis.z << std::endl;
    float multipler = 0.5f;
    if (type == 0)
    {
        cameraUp += (axis*glm::vec3(angle*cameraSpeed*multipler));
        // cameraUp = glm::normalize(cameraUp);
        std::cout << "camera UP: " << cameraUp.x << " " << cameraUp.y << " " << cameraUp.z << std::endl;
    }
    
    if (type == 1)
    {    
        cameraPos += (axis*glm::vec3(angle*cameraSpeed*multipler));
        // cameraPos = glm::normalize(cameraPos);
        std::cout << "camera POS: " << cameraPos.x << " " << cameraPos.y << " " << cameraPos.z << std::endl;
    }
    
    if (type == 2)
    {    
        cameraFront += (axis*glm::vec3(angle*cameraSpeed*multipler));
        // cameraFront = glm::normalize(cameraFront);
        std::cout << "camera FRONT: " << cameraFront.x << " " << cameraFront.y << " " << cameraFront.z << std::endl;
    }
}

void VulkanModel::rotate(float angle, glm::vec3 axis)
{
    // if (angle < 0) { m_angle = 0; }
    m_update = true;
    m_angle += angle;
    m_axis = axis;
    cameraUp += (axis*glm::vec3(angle*cameraSpeed*.01));
    cameraUp = glm::normalize(cameraUp);
    std::cout << "camera UP: " << cameraUp.x << " " << cameraUp.y << " " << cameraUp.z << std::endl;
}


void VulkanModel::switchActiveObject()
{
    uint32_t numObjectsInScene = m_scene->meshbuffer()->models().size();
    m_currentActiveObjectIndex = (m_currentActiveObjectIndex + 1) % (numObjectsInScene-1);
    // std::cout << "currently active object: " << m_currentActiveObjectIndex << std::endl;
}

template <typename T> int sgn(T val)
{
    return (T(0) < val) - (val < T(0));
}

void VulkanModel::moveObject(glm::vec3 transform)
{
    float movespeed =  0.001;
    glm::vec3 mspeed(movespeed);
    // obj_transform = transform; //*mspeed;

    // if direction has changed, clear out previous model transform
    // and move in new direction
    bool bflip = false;
    for (int i = 0; i < 3; i++)
    {
        int8_t sign = sgn(transform[i]);
        if (obj_transform[i] != sign)
        {
            bflip = true;
        }
        obj_transform[i] = sign;
    }

    translateObject(m_currentActiveObjectIndex, transform*mspeed, bflip);
}

void VulkanModel::translateObject(uint32_t object_index, glm::vec3 translation, bool bflip)
{
    MeshBuffer* mbuffer = m_scene->meshbuffer();

    // mbuffer->models()[object_index] = glm::translate(mbuffer->models()[object_index], translation);
    glm::mat4 model = mbuffer->models()[object_index];
    uint32_t numVertices = mbuffer->vsizes()[object_index];
    uint32_t offset = mbuffer->offsets()[object_index];
    std::vector<TVertex> vertices;
    vertices.resize(numVertices);

    // for (int i = 0; i < 3; i++)
    // {
    //     int8_t sign = sgn(translation[i]);
    //     if (obj_transform[i] != sign)
    //     {
    //         model = glm::mat4(1.0f);
    //     }
    //     obj_transform[i] = sign;
    // }
    if (bflip)
    {
        model = glm::mat4(1.0f);
    }
    else
    {
        model = glm::translate(mbuffer->models()[object_index], translation);
    }
    // mbuffer->models()[object_index] = glm::mat4(0.0f);//model;
    // mbuffer->models()[object_index][0][0] = 0.0f;

    mbuffer->updateModel(model, object_index);
    uint32_t vindex = 0;
    for (uint32_t v = offset; v < offset+numVertices; v++)
    {
        glm::vec4 pos = mbuffer->models()[object_index] * glm::vec4(mbuffer->vertices()[v].position, 1.0f);
        vertices[vindex] = mbuffer->vertices()[v];
        vertices[vindex].position = glm::vec3(pos.x, pos.y, pos.z);
        mbuffer->updateVertex(vertices[vindex], v);
        vindex++;
        // mbuffer->vertices()[v].position = glm::vec3(pos.x, pos.y, pos.z);
        // vertices[v] = mbuffer->vertices()[v];
    }
    // m_shader->updateVertexBuffer(vertices, offset);
    m_shader->updateVertexBuffer(vertices, object_index * sizeof(vertices[0])*vertices.size());
}

void VulkanModel::draw(float tick)
{
    std::vector<VkFence> inFlightFences = m_fences->find("inflight")->set();
    std::vector<VkSemaphore> imageAvailableSemaphores = m_semaphores->find("imageAvailable")->set();
    std::vector<VkSemaphore> renderFinishedSemaphores = m_semaphores->find("renderFinished")->set();
    vkWaitForFences(m_device, 1, &inFlightFences[m_frameIndex], VK_TRUE, UINT64_MAX);

    uint32_t imageIndex;
    VkResult result = vkAcquireNextImageKHR(m_device, m_swapchain.chain(), UINT64_MAX, imageAvailableSemaphores[m_frameIndex], VK_NULL_HANDLE, &imageIndex);

    if (result == VK_ERROR_OUT_OF_DATE_KHR) 
    {
        // m_swapchain.rebuild();
        rebuildSwapchain();
        return;
    } 
    else if (result != VK_SUCCESS && result != VK_SUBOPTIMAL_KHR) 
    {
        throw std::runtime_error("failed to acquire swap chain image!");
    }

    // update shaders
    VkExtent2D extent = m_swapchain.extent();
    // std::vector<void*> uniformBuffersMapped;
    // glm::mat4 view = glm::lookAt(cameraPos, -(cameraFront + cameraPos), cameraUp);
    glm::mat4 view = glm::lookAt(cameraPos, cameraFront /*-glm::vec3(2)*cameraPos*/, cameraUp);
    m_shader->update(tick, m_frameIndex, view);

    // object model transformation
    float movespeed =  0.00000001;
    glm::vec3 translation(-movespeed, movespeed, 0.0);

    // update an object in mesh buffer at index
    // translateObject(0, obj_transform*glm::vec3(movespeed));
    // translateObject(1, glm::vec3(movespeed, -movespeed, 0.0));
    // translateObject(2, glm::vec3(0.0, movespeed, 0.0));
    // translateObject(3, glm::vec3(-movespeed, 0.0, 0.0));

    vkResetFences(m_device, 1, &inFlightFences[m_frameIndex]);
    vkResetCommandBuffer(m_commandBuffers[m_frameIndex], 0);

    std::vector<VkDescriptorSet> descriptorSets;
    descriptorSets.push_back(m_shader->descriptorSets()[m_frameIndex]);
    // if (bUpdateRecordCommands[m_frameIndex])
    // {
        VulkanModelSupport::recordCommandBuffer(m_commandBuffers[m_frameIndex], imageIndex, m_renderpass, extent, m_framebuffers[m_frameIndex], m_pipelines[0], 
                            m_shader->vertexBuffers(), m_shader->indexBuffer(), m_layout, descriptorSets, m_indicesCount, m_vertsCount,
                            m_device, m_vertices, m_indices, m_queues[0], m_commandPool, m_memProperties);
        // bUpdateRecordCommands = false;
    // }

    descriptorSets.clear();
    
    std::vector<VkSemaphore> waitSemaphores;
    waitSemaphores.push_back(imageAvailableSemaphores[m_frameIndex]);
    VkPipelineStageFlags waitStages[] = {VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT};
    
    std::vector<VkSemaphore> signalSemaphores;
    signalSemaphores.push_back(renderFinishedSemaphores[m_frameIndex]);
    
    std::vector<VkSwapchainKHR> swapChains;
    swapChains.push_back(m_swapchain.chain());

    std::vector<VkCommandBuffer> submitBuffers;
    submitBuffers.push_back(m_commandBuffers[m_frameIndex]);

    VkSubmitInfo csubmitInfo{};
    csubmitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    csubmitInfo.pNext = NULL;
    csubmitInfo.waitSemaphoreCount = waitSemaphores.size();
    csubmitInfo.pWaitSemaphores = waitSemaphores.data();
    csubmitInfo.pWaitDstStageMask = waitStages;
    csubmitInfo.commandBufferCount = submitBuffers.size();
    csubmitInfo.pCommandBuffers = submitBuffers.data();
    csubmitInfo.signalSemaphoreCount = signalSemaphores.size();
    csubmitInfo.pSignalSemaphores = signalSemaphores.data();
    if (vkQueueSubmit(m_queues[0], 1, &csubmitInfo, inFlightFences[m_frameIndex]) != VK_SUCCESS)
    {
        throw std::runtime_error("failed to submit draw command buffer!");
    }

    VkPresentInfoKHR presentInfo{};
    presentInfo.sType = VK_STRUCTURE_TYPE_PRESENT_INFO_KHR;
    presentInfo.pNext = NULL;
    presentInfo.waitSemaphoreCount = waitSemaphores.size();
    presentInfo.pWaitSemaphores = signalSemaphores.data();
    presentInfo.swapchainCount = swapChains.size();
    presentInfo.pSwapchains = swapChains.data();
    presentInfo.pImageIndices = &imageIndex;
    result = vkQueuePresentKHR(m_queues[0], &presentInfo);

    if (result == VK_ERROR_OUT_OF_DATE_KHR || result == VK_SUBOPTIMAL_KHR || m_framebufferResized)
    {
        m_framebufferResized = false;
        // m_swapchain.rebuild();
        rebuildSwapchain();
    }
    else if (result != VK_SUCCESS)
    {
        throw std::runtime_error("failed to present swap chain image!");
    }

    m_frameIndex = (m_frameIndex + 1) % ogun::constants::MAX_FRAMES_IN_FLIGHT;
}


void VulkanModel::handleCursor(float xpos, float ypos)
{
    m_cursorPosition.x = xpos;
    m_cursorPosition.y = ypos;
}

void VulkanModel::handleMouse(double xpos, double ypos)
{
    if (firstMouse)
    {
        lastX = xpos;
        lastY = ypos;
        firstMouse = false;
    }

    float xoffset = xpos - lastX;
    float yoffset = lastY - ypos; 
    lastX = xpos;
    lastY = ypos;

    float sensitivity = 1.5f;
    xoffset *= sensitivity;
    yoffset *= sensitivity;

    yaw   += xoffset;
    pitch += yoffset;

    // if(pitch > 89.0f)
    //     pitch = 89.0f;
    // if(pitch < -89.0f)
    //     pitch = -89.0f;

    roll += sensitivity;

    glm::vec3 direction;
    direction.x = cos(glm::radians(yaw)) * cos(glm::radians(pitch));
    direction.y = sin(glm::radians(pitch));
    direction.z = sin(glm::radians(yaw)) * cos(glm::radians(pitch));
    // glm::vec3 dnorm = glm::normalize(direction);
    glm::vec3 dnorm = glm::normalize(glm::vec3(-xpos, -ypos, 0.0));
    // cameraFront = glm::vec3(-(xpos / 10)+4.8, (ypos / 10)-3, 1.0);
}

void VulkanModel::rebuildPipeline(std::vector<VShader> shaders)
{
    VGraphicsPipeline gpipeline;
    gpipeline.device(m_device)
             .pass(m_renderpass)
             .extent(m_swapchain.extent())
             .layout(m_descriptorSetLayout)
             .shaders(shaders)
             .samples(m_msaaSamples)
             .build();
    vkDestroyPipeline(m_device, m_pipelines[0], nullptr);
    vkDestroyPipelineLayout(m_device, m_layout, nullptr);
    m_pipelines.pop_back();
    m_pipelines.push_back(gpipeline.pipeline());
    m_layout = gpipeline.pipelineLayout();
    m_shaders = shaders;
}

void VulkanModel::rebuildPipeline(VkPolygonMode mode)
{
    VGraphicsPipeline gpipeline;
    gpipeline.device(m_device)
             .pass(m_renderpass)
             .extent(m_swapchain.extent())
             .layout(m_descriptorSetLayout)
             .shaders(m_shaders)
             .samples(m_msaaSamples)
             .mode(mode)
             .build();
    vkDestroyPipeline(m_device, m_pipelines[0], nullptr);
    vkDestroyPipelineLayout(m_device, m_layout, nullptr);
    m_pipelines.pop_back();
    m_pipelines.push_back(gpipeline.pipeline());
    m_layout = gpipeline.pipelineLayout();
}

void VulkanModel::recompileShaders()
{
    std::string assetPath = "/dev/projects/oguntestsandbox/assets";

    std::filesystem::path mount = "D:";
    std::filesystem::path compilerPath = mount / "/global/VulkanSDK/1.3.296.0/Bin";
    std::string compilerExe = "glslc.exe";
    std::filesystem::path compiler = mount / "/global/VulkanSDK/1.3.296.0/Bin/" / compilerExe;

    // std::filesystem::path shaderLibraryPath = mount / "/dev/projects/v0.0.1/ogunv2/ogun/assets/shaders/";
    std::filesystem::path shaderLibraryPath = mount / assetPath / "shaders/";
    std::string shaderType = "lighting";
    std::string shader = "default_lighting";
    // std::vector<std::string> shaderExts = {".vert", ".frag", ".geom"};
    std::vector<std::string> shaderExts = {".vert", ".frag"};
    std::vector<std::filesystem::path> shaders;
    shaders.push_back(shaderLibraryPath / shaderType / (shader + shaderExts[0]));
    shaders.push_back(shaderLibraryPath / shaderType / (shader + shaderExts[1]));
    // shaders.push_back(shaderLibraryPath / shaderType / (shader + shaderExts[2]));

    std::vector<std::string> shaderCmds = {};
    for (auto sdr : shaders)
    {
        std::string cmd = compiler.string() + " " + sdr.string() + " -o " + sdr.string() + ".spv";
        shaderCmds.push_back(cmd);
    }

    for (std::string cmd : shaderCmds)
    {
        system(cmd.c_str());
    }

    // shader files 
    std::vector<std::filesystem::path> shaderFiles;
    shaderFiles.push_back(std::filesystem::path(shaderLibraryPath) / shaderType / "default_lighting.vert.spv");
    // shaderFiles.push_back(std::filesystem::path(shaderLibraryPath) / shaderType / "default_lighting.geom.spv");
    shaderFiles.push_back(std::filesystem::path(shaderLibraryPath) / shaderType / "default_lighting.frag.spv");
    // shaderFiles.push_back(std::filesystem::path(shaderLibraryPath) / shaderType / "default_lighting.comp.spv");

    // VK_SHADER_STAGE_VERTEX_BIT = 0x00000001,
    // VK_SHADER_STAGE_TESSELLATION_CONTROL_BIT = 0x00000002,
    // VK_SHADER_STAGE_TESSELLATION_EVALUATION_BIT = 0x00000004,
    // VK_SHADER_STAGE_GEOMETRY_BIT = 0x00000008,
    // VK_SHADER_STAGE_FRAGMENT_BIT = 0x00000010,
    // VK_SHADER_STAGE_COMPUTE_BIT = 0x00000020,

    std::vector<VShader> m_shaders;
    VShader shader0;
    shader0.name(shaderFiles[0].string())
        .stage(VK_SHADER_STAGE_VERTEX_BIT)
        .device(m_device)
        .build();
    m_shaders.push_back(shader0);

    // VShader shader2;
    // shader2.name(shaderFiles[1].string())
    //     .stage(VK_SHADER_STAGE_GEOMETRY_BIT)
    //     .device(m_device)
    //     .build();
    // m_shaders.push_back(shader2);

    VShader shader1;
    shader1.name(shaderFiles[1].string())
        .stage(VK_SHADER_STAGE_FRAGMENT_BIT)
        .device(m_device)
        .build();
    m_shaders.push_back(shader1);

    // VShader shader2;
    // shader2.name(shaderFiles[2].string())
    //     .stage(VK_SHADER_STAGE_COMPUTE_BIT)
    //     .device(m_device)
    //     .build();
    // m_shaders.push_back(shader2);

    // m_pipelineManager->rebuild(0, shaders);
    rebuildPipeline(m_shaders);
}

void VulkanModel::resizeFramebuffer(uint32_t width, uint32_t height)
{
    m_framebufferResized = true;
    m_height = height;
    m_width = width;
}

void VulkanModel::rebuildSwapchain()
{
    vkDeviceWaitIdle(m_device);
    cleanupSwapchain();
    createSwapchain();
    VulkanModelSupport::createColorResources(m_device, m_swapchain.format(), m_deviceinfo.msaaSamples, m_colorImage, m_colorImageMemory, m_swapchain.extent(), m_deviceinfo.memoryProperties, 1u, m_colorImageView);
    VulkanModelSupport::createDepthResources(m_device, m_pdevice, m_deviceinfo.msaaSamples, m_depthImage, m_depthImageMemory, m_swapchain.extent(), m_deviceinfo.memoryProperties, 1u, m_depthImageView);
    VulkanModelSupport::createFramebuffers(m_device, m_swapchain.extent(), m_renderpass, m_colorImageView, m_depthImageView, m_swapchain.imageViews(), m_framebuffers);
}

void VulkanModel::createSwapchain()
{
    SwapChainSupportDetails details = querySwapchainSupport(m_pdevice, m_surface);
    VkExtent2D extent{m_width, m_height};
    VSwapchain swapchain;
    swapchain.device(m_device)
             .depth(m_deviceinfo.depthFormat)
             .surface(m_surface)
             .extent(extent)
             .presentModes(details.presentModes)
             .capabilities(details.capabilities)
             .formats(details.formats)
             .build(m_instance, m_pindices);
    m_swapchain = swapchain;
}

void VulkanModel::cleanupSwapchain()
{
    vkDestroyImageView(m_device, m_depthImageView, nullptr);
    vkDestroyImage(m_device, m_depthImage, nullptr);
    vkFreeMemory(m_device, m_depthImageMemory, nullptr);

    vkDestroyImageView(m_device, m_colorImageView, nullptr);
    vkDestroyImage(m_device, m_colorImage, nullptr);
    vkFreeMemory(m_device, m_colorImageMemory, nullptr);

    for (auto framebuffer : m_framebuffers) {
        vkDestroyFramebuffer(m_device, framebuffer, nullptr);
    }

    for (auto imageView : m_swapchain.imageViews()) {
        vkDestroyImageView(m_device, imageView, nullptr);
    }

    vkDestroySwapchainKHR(m_device, m_swapchain.chain(), nullptr);
}

SwapChainSupportDetails VulkanModel::querySwapchainSupport(VkPhysicalDevice device, VkSurfaceKHR surface)
{
    SwapChainSupportDetails details;

    vkGetPhysicalDeviceSurfaceCapabilitiesKHR(device, surface, &details.capabilities);

    uint32_t formatCount;
    vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &formatCount, nullptr);

    if (formatCount != 0) {
        details.formats.resize(formatCount);
        vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &formatCount, details.formats.data());
    }

    uint32_t presentModeCount;
    vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &presentModeCount, nullptr);

    if (presentModeCount != 0) {
        details.presentModes.resize(presentModeCount);
        vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &presentModeCount, details.presentModes.data());
    }

    return details;
}