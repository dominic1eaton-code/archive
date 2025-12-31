/**
 * @brief   Default top level frame buffer for render application
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
    , m_fixedViewportSpecified(true)
    , m_fixedScissorSpecified(false)
{
    m_logger = new LoggingTool::Logger();
    m_logger->enable();
    m_meshBuffer = new VertexBuffer(device, memoryProperties);
    m_stageBuffer = new StageBuffer(device, memoryProperties);
    m_meshIndexBuffer = new IndexBuffer(device, memoryProperties);
    initialize();
}

ColorPass::~ColorPass()
{
    // vkDestroyDevice(m_ColorPass, nullptr);
}

void ColorPass::initialize()
{
    // init UBO and descriptor sets
    VkDeviceSize cameraBufferSize = sizeof(GPUCamera);
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

    // fixed view port
    m_fixedviewport.x = 0.0f;
    m_fixedviewport.y = 0.0f;
    m_fixedviewport.width = (float) m_swapChainExtent.width;
    m_fixedviewport.height = (float) m_swapChainExtent.height;
    m_fixedviewport.minDepth = 0.0f;
    m_fixedviewport.maxDepth = 1.0f;

    // fixed scissor
    m_fixedscissor.offset = {0, 0};
    m_fixedscissor.extent = m_swapChainExtent;
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

void ColorPass::draw(VkCommandBuffer commandBuffer, VkCommandPool commandPool, uint32_t imageIndex, VkQueue transferQueue, std::vector<Mesh*> meshes, std::vector<Light*> lights, std::vector<Camera*> cameras)
{
    // begin command buffer record
    begin(commandBuffer, imageIndex);

    /* process logical scene objects and bind them to GPU render objects */
    /* allocate UBOs */
    // cameras
    for (auto camera : cameras)
    {
        memcpy(m_cameraBuffers[imageIndex]->buffersMapped(), &camera->data(), sizeof(camera->data()));
        glm::vec3 viewPosition = camera->position;
    }

    // lights
    m_lightBuffers[imageIndex]->map();
    GPULight* lightSSBO = (GPULight*)m_lightBuffers[imageIndex]->buffersMapped();
    for (int lightIndex=0; lightIndex<lights.size(); lightIndex++)
    {
        lightSSBO[lightIndex].position = lights[lightIndex]->gpu().position;
        lightSSBO[lightIndex].ambient = lights[lightIndex]->gpu().ambient;
        lightSSBO[lightIndex].diffuse = lights[lightIndex]->gpu().diffuse;
        lightSSBO[lightIndex].specular = lights[lightIndex]->gpu().specular;
    }
    m_lightBuffers[imageIndex]->unmap();

    /* allocate push constants */
    // fragment shader data
    FragData fragData;
    fragData.viewPosition = viewPosition;
    fragData.numLights = lights.size();
    vkCmdPushConstants(commandBuffer, m_pipeline->layout(), VK_SHADER_STAGE_FRAGMENT_BIT, 0, sizeof(FragData), &fragData);

    // meshes
    for (int robj=0; robj<renderobjects.size(); robj++)
    {
        /* bind object data */
        // material
        m_materialBuffers[imageIndex]->map();
        GPUMaterial materialSSBO = (GPUMaterial*)m_materialBuffers[imageIndex]->buffersMapped();
        for (int lightIndex=0; lightIndex<lights.size(); lightIndex++)
        {
            materialSSBO.ambient = meshes[robj]->material().ambient;
            materialSSBO.diffuse = meshes[robj]->material().diffuse;
            materialSSBO.specular = meshes[robj]->material().specular;
            materialSSBO.shine = meshes[robj]->material().shine;
        }
        m_materialBuffers[imageIndex]->unmap();

        // vertices
        const std::vector<Vertex> verts = meshes[robj]->vertices();
        const std::vector<uint16_t> inds = meshes[robj]->indices();

        VkDeviceSize vertsSize = verts.size() * sizeof(Vertex);
        m_meshBuffer->allocate(vertsSize);
        m_stageBuffer->allocate(vertsSize);
        m_stageBuffer->map(verts);
        copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshBuffer->buffer(), vertsSize);
        m_stageBuffer->deallocate();

        // allocate indices
        if (meshes[robj]->indexed())
        {
            VkDeviceSize indsSize = sizeof(inds[0]) * inds.size();
            m_meshIndexBuffer->allocate(indsSize);
            m_stageBuffer->allocate(indsSize);
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
        
        if (meshes[robj]->indexed())
            vkCmdBindIndexBuffer(commandBuffer, m_meshIndexBuffer->buffer(), 0, VK_INDEX_TYPE_UINT16);

        vkCmdBindDescriptorSets(commandBuffer, m_pipeline->bindpoint(), m_pipeline->layout(), 0, 1, &m_descriptorSets[imageIndex], 0, nullptr);

        // binding render area
        if (m_fixedViewportSpecified)
            vkCmdSetViewport(commandBuffer, 0, 1, &m_fixedviewport);

        if (m_fixedScissorSpecified)
            vkCmdSetScissor(commandBuffer, 0, 1, &m_fixedscissor);

        // draw
        if (meshes[robj]->indexed())
        {
            vkCmdDrawIndexed(commandBuffer, static_cast<uint32_t>(inds.size()), 1, 0, 0, 0);
        }
        else
        {
            vkCmdDraw(commandBuffer, static_cast<uint32_t>(verts.size()), 1, 0, 0);
        }
    }

    // end command buffer record
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
