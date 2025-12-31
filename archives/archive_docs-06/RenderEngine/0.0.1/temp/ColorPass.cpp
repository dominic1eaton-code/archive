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
#include <chrono>
#include <glm/gtc/matrix_transform.hpp>

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
        m_cameraBuffers[i] = new UniformBuffer(device, memoryProperties);
        m_cameraBuffers[i]->allocate(cameraBufferSize);
        m_cameraBuffers[i]->map();
    }
}

ColorPass::~ColorPass()
{
    // vkDestroyDevice(m_ColorPass, nullptr);
}


std::vector<UniformBuffer*> ColorPass::uniformBuffers()
{
    return m_cameraBuffers;
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
    VkClearValue clearColor = {{{0.0f, 0.0f, 0.0f, 1.0f}}};
    m_renderPassInfo.clearValueCount = 1;
    m_renderPassInfo.pClearValues = &clearColor;

    // The first parameter for every command is always the command buffer to record the command to. The
    // second parameter specifies the details of the render pass we've just provided. The final parameter
    // controls how the drawing commands within the render pass will be provided. It can have one of two values:
    //     VK_SUBPASS_CONTENTS_INLINE                   : The render pass commands will be embedded in the
    //                                                    primary command buffer itself and no secondary command
    //                                                     buffers will be executed.
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

    CameraData camera;
    camera.model = glm::rotate(glm::mat4(1.0f), time * glm::radians(90.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    camera.view = glm::lookAt(glm::vec3(3.0f, 3.0f, 1.0f), glm::vec3(0.0f, 0.0f, 0.0f), glm::vec3(0.0f, 0.0f, 1.0f));
    camera.proj = glm::perspective(glm::radians(45.0f), m_swapChainExtent.width / (float) m_swapChainExtent.height, 0.1f, 10.0f);
    camera.proj[1][1] *= -1;
    memcpy(m_cameraBuffers[imageIndex]->buffersMapped(), &camera, sizeof(camera));
    // m_cameraBuffers[imageIndex]->copy(camera);
    
    // allocate vertices
    std::vector<const std::vector<Vertex>*> vertices;
    std::vector<const std::vector<uint16_t>*> indices;
    for (int rObj=0; rObj<meshes.size(); rObj++)
    {
        // const std::vector<Vertex> verts = meshes[rObj]->vertices();
        vertices.push_back(&meshes[rObj]->vertices());
        VkDeviceSize vertsBufferSize = vertices[0]->size() * sizeof(Vertex);
        m_meshBuffer->allocate(vertsBufferSize);  // @todo call in initialize function
        m_stageBuffer->allocate(vertsBufferSize); // @todo call in initialize function
        m_stageBuffer->map(*vertices[0]);
        copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshBuffer->buffer(), vertsBufferSize);
        m_stageBuffer->deallocate();

        // allocate indices
        // const std::vector<uint16_t> inds = meshes[rObj]->indices();
        indices.push_back(&meshes[rObj]->indices());
        VkDeviceSize indBufferSize = sizeof(indices[0][0]) * indices[0]->size();
        m_meshIndexBuffer->allocate(indBufferSize); // @todo call in initialize function
        m_stageBuffer->allocate(indBufferSize);     // @todo call in initialize function
        m_stageBuffer->map(*indices[0]);
        copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshIndexBuffer->buffer(), indBufferSize);
        m_stageBuffer->deallocate();
    }

    /*
        std::vector<Vertex> mergedVertexBuffer;
        std::vector<uint16_t> mergedIndexBuffer;
        VkDeviceSize mergedVertexBufferSize = 0;
        VkDeviceSize mergedIndexBufferSize = 0;
        uint32_t indicesSize = 0;
        for (int rObj=0; rObj<meshes.size(); rObj++)
        {
            // // allocate vertices
            // const std::vector<Vertex> verts = meshes[rObj]->vertices();
            // VkDeviceSize vertsSize = verts.size() * sizeof(Vertex);
            // mergedVertexBufferSize = mergedVertexBufferSize + vertsSize;

            // allocate indices
            if (meshes[rObj]->indexed())
            {
                const std::vector<Vertex> verts = meshes[rObj]->vertices();
                VkDeviceSize vertsSize = verts.size() * sizeof(Vertex);
                mergedVertexBufferSize = mergedVertexBufferSize + vertsSize;

                const std::vector<uint16_t> inds = meshes[rObj]->indices();
                VkDeviceSize indsSize = sizeof(inds[0]) * inds.size();
                mergedIndexBufferSize = mergedIndexBufferSize + indsSize;
            
                mergedVertexBuffer.insert(mergedVertexBuffer.end(), verts.begin(), verts.end());
                mergedIndexBuffer.insert(mergedIndexBuffer.end(), inds.begin(), inds.end());
            }
        }
        const std::vector<Vertex> mergedVertices = mergedVertexBuffer;
        const std::vector<uint16_t> mergedIndices = mergedIndexBuffer;
    */

    /*
    std::vector<Vertex> mergedVertexBuffer;
    std::vector<uint16_t> mergedIndexBuffer;
    uint32_t indicesSize = 0;
    for (int rObj=0; rObj<meshes.size(); rObj++)
    {
        // allocate vertices
        const std::vector<Vertex> verts = meshes[rObj]->vertices();
        VkDeviceSize vertsBufferSize = verts.size() * sizeof(Vertex);
        m_meshBuffer->allocate(vertsBufferSize);  // @todo call in initialize function
        m_stageBuffer->allocate(vertsBufferSize); // @todo call in initialize function
        m_stageBuffer->map(verts);
        copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshBuffer->buffer(), vertsBufferSize);
        m_stageBuffer->deallocate();

        // allocate indices
        if (meshes[rObj]->indexed())
        {
            const std::vector<uint16_t> inds = meshes[rObj]->indices();
            VkDeviceSize indBufferSize = sizeof(inds[0]) * inds.size();
            m_meshIndexBuffer->allocate(indBufferSize); // @todo call in initialize function
            m_stageBuffer->allocate(indBufferSize);     // @todo call in initialize function
            m_stageBuffer->map(inds);
            copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshIndexBuffer->buffer(), indBufferSize);
            m_stageBuffer->deallocate();
            indicesSize = indicesSize + static_cast<uint32_t>(inds.size());

            mergedVertexBuffer.insert(mergedVertexBuffer.end(), verts.begin(), verts.end());
            mergedIndexBuffer.insert(mergedIndexBuffer.end(), inds.begin(), inds.end());
        }
    }
    */

   /*
    // merge mesh buffers
    uint32_t indicesSize = 0;
    VkDeviceSize verticesBufferSize = 0;
    VkDeviceSize indicesBufferSize = 0;
    std::vector<Vertex> vertTotal;
    std::vector<uint16_t> indTotal;
    for (int rObj=0; rObj<meshes.size(); rObj++)
    {
        const std::vector<Vertex> verts = meshes[rObj]->vertices();
        VkDeviceSize vertsBufferSize = verts.size() * sizeof(Vertex);

        // allocate indices
        const std::vector<uint16_t> inds = meshes[rObj]->indices();
        VkDeviceSize indBufferSize = sizeof(inds[0]) * inds.size();

        indicesSize = indicesSize + static_cast<uint32_t>(inds.size());
        verticesBufferSize = verticesBufferSize + vertsBufferSize;
        indicesBufferSize = indicesBufferSize + indBufferSize;

        vertTotal.insert(vertTotal.end(), verts.begin(), verts.end());
        indTotal.insert(indTotal.end(), inds.begin(), inds.end());
    }
    const std::vector<Vertex> vertTotalBuffer = vertTotal;
    const std::vector<uint16_t> indTotalBuffer = indTotal;

    m_meshBuffer->allocate(verticesBufferSize);      // @todo call in initialize function
    m_stageBuffer->allocate(verticesBufferSize);     // @todo call in initialize function
    m_stageBuffer->map(vertTotalBuffer);
    copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshBuffer->buffer(), verticesBufferSize);
    m_stageBuffer->deallocate();

    m_meshIndexBuffer->allocate(indicesBufferSize); // @todo call in initialize function
    m_stageBuffer->allocate(indicesBufferSize);     // @todo call in initialize function
    m_stageBuffer->map(indTotalBuffer);
    copyBuffer(commandBuffer, commandPool, transferQueue, m_stageBuffer->buffer(), m_meshIndexBuffer->buffer(), verticesBufferSize);
    m_stageBuffer->deallocate();
   */

    /* bind drawing commands */
    // The second parameter specifies if the pipeline object is a graphics or compute pipeline.
    // We've now told Vulkan which operations to execute in the graphics pipeline and which
    // attachment to use in the fragment shader
    vkCmdBindPipeline(commandBuffer, m_pipeline->bindpoint(), m_pipeline->pipeline()); // @todo handle multiple pipelines

    // binding data buffers
    VkBuffer vertexBuffers[] = {m_meshBuffer->buffer()};
    VkDeviceSize offsets[] = {0};
    vkCmdBindVertexBuffers(commandBuffer, 0, 1, vertexBuffers, offsets);
    vkCmdBindIndexBuffer(commandBuffer, m_meshIndexBuffer->buffer(), 0, VK_INDEX_TYPE_UINT16);
    vkCmdBindDescriptorSets(commandBuffer, m_pipeline->bindpoint(), m_pipeline->layout(), 0, 1, &m_descriptorSets[imageIndex], 0, nullptr);

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
    
    // vkCmdDraw(commandBuffer, static_cast<uint32_t>(verts.size()), 1, 0, 0);
    vkCmdDrawIndexed(commandBuffer, static_cast<uint32_t>(indices.size()), 1, 0, 0, 0);
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
