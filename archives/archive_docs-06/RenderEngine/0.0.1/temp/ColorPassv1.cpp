/**
 * @brief   Default top level frame buffer for render application. Translates data about primitives
 *          into vk draw commands to be executed. Primitives: Mesh, Camera, Light, Terrain, Environment, Undefined
 * @note    N/A
 * @version 0.1
 * @copyright Copyright (c) 2023
 */
#include "ColorPass.h"
#include "GraphicsPipeline.h"
#include "Logger.h"
#include "VulkanCommon.h"
#include "VulkanConstants.h"
#include <SDL2/SDL.h>
#include "Buffer/VertexBuffer.h"
#include "Buffer/StageBuffer.h"
#include "Buffer/IndexBuffer.h"
#include "Buffer/UniformBuffer.h"
#include "Buffer/Descriptor.h"
#include "Math/Triangle.h"
#include "Scene/Camera.h"
#include "Scene/Light.h"
#include "Scene/Mesh.h"
#include <chrono>
#include <glm/gtc/matrix_transform.hpp>
#include "Math/Vertex.h"

using namespace RenderEngine;

ColorPass::ColorPass()
{}

ColorPass::ColorPass(VkDevice device, VkExtent2D swapChainExtent, std::vector<VkFramebuffer> swapChainFramebuffers, GraphicsPipeline* pipeline, VkPhysicalDeviceMemoryProperties memoryProperties, std::vector<VkDescriptorSet> descriptorSets)
    : m_subpassContents(VK_SUBPASS_CONTENTS_INLINE)
    , m_renderPassInfo({})
    , m_swapChainExtent(swapChainExtent)
    , m_swapChainFramebuffers(swapChainFramebuffers)
    , m_pipeline(pipeline)
    , m_memoryProperties(memoryProperties)
    , m_device(device)
    , m_descriptorSets(descriptorSets)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    m_meshBuffer = new VertexBuffer(device, memoryProperties);
    m_stageBuffer = new StageBuffer(device, memoryProperties);
    m_meshIndexBuffer = new IndexBuffer(device, memoryProperties);

    // init UBO and descriptor sets
    VkDeviceSize cameraBufferSize = sizeof(CameraData);
    m_cameraBuffers.resize(Constants::MAX_FRAMES_IN_FLIGHT);
    for (int i=0; i<m_cameraBuffers.size(); i++)
    {
        m_cameraBuffers[i] = new UniformBuffer(device, memoryProperties, VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER, 0);
        m_cameraBuffers[i]->allocate(cameraBufferSize);
        m_cameraBuffers[i]->map();
    }

    VkDeviceSize lightBufferSize = sizeof(LightData);
    m_lightBuffers.resize(Constants::MAX_FRAMES_IN_FLIGHT);
    for (int i=0; i<m_lightBuffers.size(); i++)
    {
        m_lightBuffers[i] = new UniformBuffer(device, memoryProperties, VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, 1, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT);
        m_lightBuffers[i]->allocate(lightBufferSize);
    }
}

ColorPass::~ColorPass()
{
    // vkDestroyDevice(m_ColorPass, nullptr);
}

std::vector<std::vector<UniformBuffer*>> ColorPass::uniformBuffers()
{
    std::vector<std::vector<UniformBuffer*>> ubos;
    ubos.resize(2);
    ubos[0] = m_cameraBuffers;
    ubos[1] = m_lightBuffers;
    return ubos;
}

void ColorPass::begin(VkCommandBuffer commandBuffer, uint32_t imageIndex)
{
    // Drawing starts by beginning the render pass
    m_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;

    // The first parameters are the render pass itself and the attachments to bind. We created
    // a framebuffer for each swap chain image where it is specified as a color attachment. Thus
    // we need to bind the framebuffer for the swapchain image we want to draw to. Using the
    // imageIndex parameter which was passed in, we can pick the right framebuffer for the
    // current swapchain image.
    m_renderPassInfo.renderPass = m_pipeline->renderPass();
    m_renderPassInfo.framebuffer = m_swapChainFramebuffers[imageIndex];

    // define the size of the render area. The render area defines where shader loads and stores will
    // take place. The pixels outside this region will have undefined values. It should match the size
    // of the attachments for best performance
    m_renderPassInfo.renderArea.offset = {0, 0};
    m_renderPassInfo.renderArea.extent = m_swapChainExtent;

    // The last two parameters define the clear values to use for VK_ATTACHMENT_LOAD_OP_CLEAR, which we
    // used as load operation for the color attachment. I've defined the clear color to simply be black
    // with 100% opacity.
    std::array<VkClearValue, 2> clearValues{};
    clearValues[0].color = {{0.0f, 0.0f, 0.0f, 1.0f}};
    clearValues[1].depthStencil = {1.0f, 0};
    m_renderPassInfo.clearValueCount = static_cast<uint32_t>(clearValues.size());
    m_renderPassInfo.pClearValues = clearValues.data();

    // The first parameter for every command is always the command buffer to record the command to. The
    // second parameter specifies the details of the render pass we've just provided. The final parameter
    // controls how the drawing commands within the render pass will be provided. It can have one of two values:
    //     VK_SUBPASS_CONTENTS_INLINE                   : The render pass commands will be embedded in the
    //                                                    primary command buffer itself and no secondary command
    //                                                    buffers will be executed.
    //     VK_SUBPASS_CONTENTS_SECONDARY_COMMAND_BUFFERS: The render pass commands will be executed from secondary
    //                                                    command buffers.
    vkCmdBeginRenderPass(commandBuffer, &m_renderPassInfo, m_subpassContents);
}

void ColorPass::end(VkCommandBuffer commandBuffer)
{
    vkCmdEndRenderPass(commandBuffer);
}

void ColorPass::draw(VkCommandBuffer commandBuffer, VkCommandPool commandPool, uint32_t imageIndex, std::vector<Mesh*> meshes, VkQueue transferQueue)
{
    begin(commandBuffer, imageIndex);

    /* process logical scene objects and bind them to GPU render objects */
    // allocate UBOs
    static auto startTime = std::chrono::high_resolution_clock::now();
    auto currentTime = std::chrono::high_resolution_clock::now();
    float time = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();
    uint8_t rotationDirection = -1;
    // float update = 81; // float update = time;
    float update = time;

    // camera ubo
    CameraData cameraData;
    cameraData.position = glm::vec3(4.0f, 4.0f, 1.0f);
    cameraData.model = glm::rotate(glm::mat4(1.0f), update * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    cameraData.view = glm::lookAt(cameraData.position, glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    cameraData.proj = glm::perspective(glm::radians(45.0f), m_swapChainExtent.width / (float) m_swapChainExtent.height, 0.1f, 10.0f);
    cameraData.proj[1][1] *= -1;
    memcpy(m_cameraBuffers[imageIndex]->buffersMapped(), &cameraData, sizeof(cameraData)); // m_cameraBuffers[imageIndex]->copy(cameraData);

    // light ubo
    std::vector<LightData> lights;

    LightData light0;
    light0.position = glm::vec3(0.0f, 0.0f, 1.0f); 
    light0.color = glm::vec3(1.0f, 1.0f, 1.0f);
    light0.ambient = 0.1f;
    light0.specular = 0.1f;

    LightData light1;
    light1.position = glm::vec3(0.0f, 0.0f, 0.0f); 
    light1.color = glm::vec3(1.0f, 0.0f, 0.0f);
    light1.ambient = 0.01f;
    light1.specular = 0.01f;

    lights.push_back(light0);
    lights.push_back(light1);
    
    m_lightBuffers[imageIndex]->map();
    LightData* lightSSBO = (LightData*)m_lightBuffers[imageIndex]->buffersMapped();
    for (int lightIndex=0; lightIndex<lights.size(); lightIndex++)
    {
        // memcpy(m_lightBuffers[imageIndex]->buffersMapped(), &lights[lightIndex], sizeof(lights[lightIndex]));
        lightSSBO[lightIndex].position = lights[lightIndex].position;
        lightSSBO[lightIndex].color = lights[lightIndex].color;
        lightSSBO[lightIndex].ambient = lights[lightIndex].ambient;
        lightSSBO[lightIndex].specular = lights[lightIndex].specular;
    }
    m_lightBuffers[imageIndex]->unmap();

    // allocate push constants
    // light index push constant
    RenderObjectIndices renderObjectIndices;
    renderObjectIndices.light = 0;
    vkCmdPushConstants(commandBuffer, m_pipeline->layout(), VK_SHADER_STAGE_FRAGMENT_BIT, 0, sizeof(RenderObjectIndices), &renderObjectIndices);

    /* draw render objects */
    for (int rObj=0; rObj<meshes.size(); rObj++)
    {
        const std::vector<Vertex> verts = meshes[rObj]->vertices();
        const std::vector<uint16_t> inds = meshes[rObj]->indices();

        // allocate vertices
        VkDeviceSize vertsSize = verts.size() * sizeof(Vertex);
        m_meshBuffer->allocate(vertsSize);  // @todo call in initialize function
        m_stageBuffer->allocate(vertsSize); // @todo call in initialize function
        m_stageBuffer->map(verts);
        copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshBuffer->buffer(), vertsSize);
        m_stageBuffer->deallocate();

        // allocate indices
        if (meshes[rObj]->indexed())
        {
            VkDeviceSize indsSize = sizeof(inds[0]) * inds.size();
            m_meshIndexBuffer->allocate(indsSize); // @todo call in initialize function
            m_stageBuffer->allocate(indsSize);     // @todo call in initialize function
            m_stageBuffer->map(inds);
            copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshIndexBuffer->buffer(), indsSize);
            m_stageBuffer->deallocate(); 
        }

        /* bind drawing commands */
        // The second parameter specifies if the pipeline object is a graphics or compute pipeline.
        // We've now told Vulkan which operations to execute in the graphics pipeline and which
        // attachment to use in the fragment shader
        vkCmdBindPipeline(commandBuffer, m_pipeline->bindpoint(), m_pipeline->pipeline()); // @todo handle multiple pipelines

        // binding data buffers
        VkBuffer vertexBuffers[] = {m_meshBuffer->buffer()};
        VkDeviceSize offsets[] = {0};
        vkCmdBindVertexBuffers(commandBuffer, 0, 1, vertexBuffers, offsets);
        
        if (meshes[rObj]->indexed())
            vkCmdBindIndexBuffer(commandBuffer, m_meshIndexBuffer->buffer(), 0, VK_INDEX_TYPE_UINT16);

        vkCmdBindDescriptorSets(commandBuffer, m_pipeline->bindpoint(), m_pipeline->layout(), 0, 1, &m_descriptorSets[imageIndex], 0, nullptr);

        // allocate push constants
        // N/A

        // if (fixedViewportSpecified)
        VkViewport viewport{};
        viewport.x = 0.0f;
        viewport.y = 0.0f;
        viewport.width = (float) m_swapChainExtent.width;
        viewport.height = (float) m_swapChainExtent.height;
        viewport.minDepth = 0.0f;
        viewport.maxDepth = 1.0f;
        vkCmdSetViewport(commandBuffer, 0, 1, &viewport);

        // if (fixedScissorSpecified)
        VkRect2D scissor{};
        scissor.offset = {0, 0};
        scissor.extent = m_swapChainExtent;
        vkCmdSetScissor(commandBuffer, 0, 1, &scissor);

        // draw
        if (meshes[rObj]->indexed())
        {
            vkCmdDrawIndexed(commandBuffer, static_cast<uint32_t>(inds.size()), 1, 0, 0, 0);
        }
        else
        {
            vkCmdDraw(commandBuffer, static_cast<uint32_t>(verts.size()), 1, 0, 0);
        }
    }
    end(commandBuffer);
}


void ColorPass::draw(VkCommandBuffer commandBuffer, VkCommandPool commandPool, uint32_t imageIndex, VkQueue transferQueue, std::vector<Mesh*> meshes, std::vector<Light*> lights, std::vector<Camera*> cameras)
{
    begin(commandBuffer, imageIndex);

    /* process logical scene objects and bind them to GPU render objects */
    // allocate UBOs
    // camera ubo
    CameraData cameraData;
    for (auto camera : cameras)
    {
        memcpy(m_cameraBuffers[imageIndex]->buffersMapped(), &camera->data(), sizeof(camera->data())); // m_cameraBuffers[imageIndex]->copy(cameraData);
    }

    // light ubo
    m_lightBuffers[imageIndex]->map();
    LightData* lightSSBO = (LightData*)m_lightBuffers[imageIndex]->buffersMapped();
    for (int lightIndex=0; lightIndex<lights.size(); lightIndex++)
    {
        lightSSBO[lightIndex].position = lights[lightIndex].position;
        lightSSBO[lightIndex].color = lights[lightIndex].color;
        lightSSBO[lightIndex].ambient = lights[lightIndex].ambient;
        lightSSBO[lightIndex].specular = lights[lightIndex].specular;
    }
    m_lightBuffers[imageIndex]->unmap();

    // allocate push constants
    // light index push constant
    RenderObjectIndices renderObjectIndices;
    renderObjectIndices.light = 0;
    vkCmdPushConstants(commandBuffer, m_pipeline->layout(), VK_SHADER_STAGE_FRAGMENT_BIT, 0, sizeof(RenderObjectIndices), &renderObjectIndices);

    /* draw render objects */
    for (int rObj=0; rObj<meshes.size(); rObj++)
    {
        const std::vector<Vertex> verts = meshes[rObj]->vertices();
        const std::vector<uint16_t> inds = meshes[rObj]->indices();

        // allocate vertices
        VkDeviceSize vertsSize = verts.size() * sizeof(Vertex);
        m_meshBuffer->allocate(vertsSize);  // @todo call in initialize function
        m_stageBuffer->allocate(vertsSize); // @todo call in initialize function
        m_stageBuffer->map(verts);
        copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshBuffer->buffer(), vertsSize);
        m_stageBuffer->deallocate();

        // allocate indices
        if (meshes[rObj]->indexed())
        {
            VkDeviceSize indsSize = sizeof(inds[0]) * inds.size();
            m_meshIndexBuffer->allocate(indsSize); // @todo call in initialize function
            m_stageBuffer->allocate(indsSize);     // @todo call in initialize function
            m_stageBuffer->map(inds);
            copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshIndexBuffer->buffer(), indsSize);
            m_stageBuffer->deallocate();
        }

        /* bind drawing commands */
        // The second parameter specifies if the pipeline object is a graphics or compute pipeline.
        // We've now told Vulkan which operations to execute in the graphics pipeline and which
        // attachment to use in the fragment shader
        vkCmdBindPipeline(commandBuffer, m_pipeline->bindpoint(), m_pipeline->pipeline()); // @todo handle multiple pipelines

        // binding data buffers
        VkBuffer vertexBuffers[] = {m_meshBuffer->buffer()};
        VkDeviceSize offsets[] = {0};
        vkCmdBindVertexBuffers(commandBuffer, 0, 1, vertexBuffers, offsets);
        
        if (meshes[rObj]->indexed())
            vkCmdBindIndexBuffer(commandBuffer, m_meshIndexBuffer->buffer(), 0, VK_INDEX_TYPE_UINT16);

        vkCmdBindDescriptorSets(commandBuffer, m_pipeline->bindpoint(), m_pipeline->layout(), 0, 1, &m_descriptorSets[imageIndex], 0, nullptr);

        if (m_fixedViewportSpecified)
            vkCmdSetViewport(commandBuffer, 0, 1, &m_fixedviewport);

        if (m_fixedScissorSpecified)
            vkCmdSetScissor(commandBuffer, 0, 1, &m_fixedscissor);

        // draw
        if (meshes[rObj]->indexed())
        {
            vkCmdDrawIndexed(commandBuffer, static_cast<uint32_t>(inds.size()), 1, 0, 0, 0);
        }
        else
        {
            vkCmdDraw(commandBuffer, static_cast<uint32_t>(verts.size()), 1, 0, 0);
        }
    }
    end(commandBuffer);
}

void ColorPass::copyBuffer(VkCommandBuffer commandBuffer, VkCommandPool commandPool, VkQueue transferQueue, VkBuffer srcBuffer, VkBuffer dstBuffer, VkDeviceSize size)
{
    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandPool = commandPool;
    allocInfo.commandBufferCount = 1;

    vkAllocateCommandBuffers(m_device, &allocInfo, &commandBuffer);
    VkCommandBufferBeginInfo beginInfo{};



    beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    beginInfo.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;

    vkBeginCommandBuffer(commandBuffer, &beginInfo);
    VkBufferCopy copyRegion{};
    copyRegion.size = size;
    vkCmdCopyBuffer(commandBuffer, srcBuffer, dstBuffer, 1, &copyRegion);
    vkEndCommandBuffer(commandBuffer);

    VkSubmitInfo submitInfo{};
    submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    submitInfo.commandBufferCount = 1;
    submitInfo.pCommandBuffers = &commandBuffer;
    vkQueueSubmit(transferQueue, 1, &submitInfo, VK_NULL_HANDLE);
    vkQueueWaitIdle(transferQueue);
    vkFreeCommandBuffers(m_device, commandPool, 1, &commandBuffer);
}
