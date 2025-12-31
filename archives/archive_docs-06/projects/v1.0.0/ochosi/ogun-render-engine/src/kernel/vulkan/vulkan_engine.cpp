/**
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_shader.h"
#include "ogun_scene.h"
#include <filesystem>
#include "vulkan_engine.h"
#include <iostream>

#define BUFFER_ELEMENTS 32
namespace vulkan
{

std::vector<bool> prepared = {false, false, false};
std::vector<uint32_t> headless_compute_data_input(BUFFER_ELEMENTS);
std::vector<uint32_t> headless_compute_data_output(BUFFER_ELEMENTS);

void move_cursor(double xpos, double  ypos, glm::vec2& cursor)
{
    cursor.x = xpos;
    cursor.y = ypos;
}

void resize_frame_buffer(uint32_t width, uint32_t height, VFrame* frame)
{
    frame->window_extent = VkExtent2D{width, height};
}

void init_Vulkan(HWND hwnd, VkExtent2D window_extent, VFrame* frame)
{
    std::filesystem::path mount = std::filesystem::path("C:/");
    // std::filesystem::path asset_library_path = mount / "dev/projects/emchoro/ossain/oru/ogun/assets";
    // std::filesystem::path asset_library_path = mount / "dev/projects/ogun-render-engine/assets";
    std::filesystem::path asset_library_path = mount / "dev/projects/ogun-render-engine/assets";

    /* core objects */
    bool enable_validation = false;
    VkInstance instance;
    std::vector<const char*> pextensions = {"VK_KHR_surface", "VK_KHR_win32_surface"};
    std::vector<const char*> players = {};
    if (enable_validation) 
    {
        pextensions.push_back("VK_EXT_debug_utils");
        players.push_back("VK_LAYER_KHRONOS_validation");
    }
    create_instance(instance, pextensions, players);
    
    VkDebugUtilsMessengerEXT debugMessenger;
    if (enable_validation)
    {
        create_debugger(instance, debugMessenger);
    }

    VkSurfaceKHR surface;
    create_surface_win32(surface, instance, hwnd);

    PDevice pdevice;
    create_physical_device(pdevice, instance, surface);

    VkDevice ldevice;
    std::vector<VkQueue> queues;
    std::vector<const char*> extensions = {"VK_KHR_swapchain", "VK_KHR_shader_draw_parameters"};
    create_logical_device(ldevice, queues, pdevice.device, pdevice.pinfo.features, pdevice.qinfo, extensions);

    PSwapchain swapchain;
    PSwapchainInfo swapchain_info = {
        pdevice.pinfo.depth_format,
        pdevice.pinfo.formats,
        window_extent,
        pdevice.pinfo.present_modes,
        pdevice.pinfo.capabilities
    };
    create_swapchain(swapchain, swapchain_info, ldevice, surface);

    VkCommandPool command_pool;
    create_command_pool(command_pool, ldevice, pdevice.qinfo[0].queueFamilyIndex);
    
    std::vector<VkCommandBuffer> command_buffers;
    command_buffers.resize(constants::MAX_FRAMES_IN_FLIGHT);
    create_command_buffer(command_buffers, ldevice, command_pool);
    
    std::vector<VkCommandBuffer> compute_command_buffers;
    compute_command_buffers.resize(constants::MAX_FRAMES_IN_FLIGHT);
    create_command_buffer(compute_command_buffers, ldevice, command_pool);

    std::vector<std::vector<VkCommandBuffer>> cmds;
    cmds.push_back(command_buffers);
    cmds.push_back(compute_command_buffers);

    /* default graphics pipeline */
    VkRenderPass renderpass;
    VRenderpassInfo info = {
        swapchain.format,
        find_depth_format(pdevice.device),
        pdevice.pinfo.msaa_samples,
        VK_PIPELINE_BIND_POINT_GRAPHICS,
        {true, true}
    };
    create_renderpass(renderpass, ldevice, info);

    VImage color_image;
    create_color_image(color_image, swapchain.extent, swapchain.format, pdevice.pinfo.msaa_samples, pdevice.pinfo.memoryProperties, ldevice);
    
    VImage depth_image;
    create_depth_image(depth_image, swapchain.extent, find_depth_format(pdevice.device), pdevice.pinfo.msaa_samples, pdevice.pinfo.memoryProperties, ldevice);
    
    std::vector<VkFence> gframebuffer;
    gframebuffer.resize(constants::MAX_FRAMES_IN_FLIGHT);
    std::vector<VkImageView> framebuffer_image_views = {color_image.view, depth_image.view};
    create_framebuffer(gframebuffer, ldevice, renderpass, swapchain.extent, swapchain.views, framebuffer_image_views);

    // object picker
    VkRenderPass op_renderpass;
    VRenderpassInfo op_renderpass_info = {
        swapchain.format,
        find_depth_format(pdevice.device),
        pdevice.pinfo.msaa_samples,
        VK_PIPELINE_BIND_POINT_GRAPHICS,
        {false, true}
    };
    create_renderpass(op_renderpass, ldevice, op_renderpass_info);

    VImage op_color_image;
    create_color_image(op_color_image, swapchain.extent, swapchain.format, pdevice.pinfo.msaa_samples, pdevice.pinfo.memoryProperties, ldevice);
    
    std::vector<VkFence> op_gframebuffer;
    op_gframebuffer.resize(constants::MAX_FRAMES_IN_FLIGHT);
    std::vector<VkImageView> op_framebuffer_image_views = {op_color_image.view};
    create_framebuffer(op_gframebuffer, ldevice, op_renderpass, swapchain.extent, swapchain.views, op_framebuffer_image_views);

    frame->scene.images.push_back(color_image);
    frame->scene.images.push_back(depth_image);

    // frame data
    std::vector<VkRenderPass> renderpasses;
    std::vector<std::vector<VkFramebuffer>> framebuffers;
    renderpasses.push_back(renderpass);
    renderpasses.push_back(op_renderpass);
    framebuffers.push_back(gframebuffer);
    framebuffers.push_back(op_gframebuffer);

    // asset data
    std::vector<VShaderModule> shaders;
    std::string package = "lighting";
    std::string module = "default_lighting";
    load_shader_files(shaders, asset_library_path, package, module, ldevice);
    
    std::vector<VShaderModule> compute_shaders;
    std::string compute_package = "particle";
    std::string compute_module = "default_particle";
    load_shader_files(compute_shaders, asset_library_path, compute_package, compute_module, ldevice);

    /* input data */
    ogun::create_test_compute_data(headless_compute_data_input);

    std::vector<ogun::OMeshBuffer> meshes;
    std::vector<ogun::GPULight> lights;
    std::vector<ogun::VCamera> cameras;
    std::vector<ogun::GPUParticle> particles;
    ogun::create_test_scene(meshes, lights, cameras, particles);

    // create buffers
    VkDeviceSize dynamic_stage_buffer_size = 0;
    for (int i = 0; i < meshes.size(); i++)
    {
        dynamic_stage_buffer_size += sizeof(meshes[i].vertices[0]) * meshes[i].vertices.size();
        dynamic_stage_buffer_size += sizeof(meshes[i].indices[0]) * meshes[i].indices.size();
    }
    dynamic_stage_buffer_size += sizeof(ogun::GPULight) * lights.size();
    VBuffer stage_buffer;
    create_stage_buffer(stage_buffer, fixed_buffer_size, pdevice.pinfo.memoryProperties, ldevice);

    VSingleCommand scmd;
    scmd.device = ldevice;
    scmd.pool = command_pool;
    scmd.queue = queues[0];
    std::vector<VkDescriptorImageInfo> textures;
    VBuffer* texture_stage_buffer = new VBuffer();
    const VkDeviceSize texture_stage_buffer_size = 100000000;
    create_stage_buffer(*texture_stage_buffer, texture_stage_buffer_size, pdevice.pinfo.memoryProperties, ldevice);
    load_textures(textures, asset_library_path, *texture_stage_buffer, pdevice.device, pdevice.pinfo.memoryProperties, scmd, pdevice.pinfo.properties.limits.maxSamplerAnisotropy);
    vkDestroyBuffer(ldevice, texture_stage_buffer->buffer, nullptr);
    vkFreeMemory(ldevice, texture_stage_buffer->memory, nullptr);
    delete texture_stage_buffer;
    
    VBuffer texture_stage_buffer2;
    create_stage_buffer(texture_stage_buffer2, texture_stage_buffer_size, pdevice.pinfo.memoryProperties, ldevice);
    std::vector<VBuffer> stage_buffers;
    stage_buffers.push_back(texture_stage_buffer2);

    std::vector<std::vector<VBuffer>> shader_buffers;
    VDescriptor descriptor;
    create_descriptor(descriptor, shader_buffers, textures, ldevice, pdevice.pinfo.memoryProperties);
    
    std::vector<std::vector<VBuffer>> compute_shader_buffers;
    VDescriptor compute_descriptor;
    create_compute_descriptor(compute_descriptor, compute_shader_buffers, {}, ldevice, pdevice.pinfo.memoryProperties);
    shader_buffers.push_back(compute_shader_buffers[0]);

    VkPipelineLayout pipeline_layout;
    std::vector<VkDescriptorSetLayout> descriptor_layouts;
    descriptor_layouts.push_back(descriptor.layout);
    create_pipeline_layout(pipeline_layout, descriptor_layouts, ldevice);
    
    VkPipelineLayout compute_pipeline_layout;
    std::vector<VkDescriptorSetLayout> compute_descriptor_layouts;
    compute_descriptor_layouts.push_back(compute_descriptor.layout);
    create_pipeline_layout(compute_pipeline_layout, compute_descriptor_layouts, ldevice);

    VPipeline line_pipeline;
    // std::vector<VkDynamicState> dynamics_states = {VK_DYNAMIC_STATE_VIEWPORT, VK_DYNAMIC_STATE_SCISSOR, VK_DYNAMIC_STATE_PRIMITIVE_TOPOLOGY};
    std::vector<VkDynamicState> dynamics_states = {VK_DYNAMIC_STATE_VIEWPORT, VK_DYNAMIC_STATE_SCISSOR};
    VPipelineInfo pipeline_info = {
        VK_POLYGON_MODE_FILL,
        pdevice.pinfo.msaa_samples,
        dynamics_states,
        VK_PRIMITIVE_TOPOLOGY_LINE_LIST
    };
    create_graphics_pipeline(line_pipeline, pipeline_info, ldevice, renderpass, pipeline_layout, shaders, sema::VertexType::MESH);
    
    pipeline_info = {
        VK_POLYGON_MODE_FILL,
        pdevice.pinfo.msaa_samples,
        dynamics_states,
        VK_PRIMITIVE_TOPOLOGY_TRIANGLE_LIST
    };
    VPipeline shape_pipeline;
    create_graphics_pipeline(shape_pipeline, pipeline_info, ldevice, renderpass, pipeline_layout, shaders, sema::VertexType::MESH);

    pipeline_info = {
        VK_POLYGON_MODE_FILL,
        pdevice.pinfo.msaa_samples,
        dynamics_states,
        VK_PRIMITIVE_TOPOLOGY_POINT_LIST
    };
    VPipeline particle_pipeline;
    std::vector<VShaderModule> particle_shaders;
    particle_shaders.push_back(compute_shaders[1]);
    particle_shaders.push_back(compute_shaders[2]);
    create_graphics_pipeline(particle_pipeline, pipeline_info, ldevice, renderpass, pipeline_layout, particle_shaders, sema::VertexType::PARTICLE);

    VPipeline particle_compute_pipeline;
    create_compute_pipeline(particle_compute_pipeline, compute_pipeline_layout, compute_shaders, ldevice);

    std::vector<std::vector<VkFence>> fences;
    std::vector<VkFence> gifences;
    gifences.resize(constants::MAX_FRAMES_IN_FLIGHT);
    create_fence(gifences, VK_FENCE_CREATE_SIGNALED_BIT, ldevice);

    std::vector<VkFence> cifences;
    cifences.resize(constants::MAX_FRAMES_IN_FLIGHT);
    create_fence(cifences, VK_FENCE_CREATE_SIGNALED_BIT, ldevice);

    std::vector<std::vector<VkSemaphore>> semaphores;
    std::vector<VkSemaphore> gisemahpore;
    gisemahpore.resize(constants::MAX_FRAMES_IN_FLIGHT);
    create_semaphore(gisemahpore, ldevice);
    
    std::vector<VkSemaphore> grsemahpore;
    grsemahpore.resize(constants::MAX_FRAMES_IN_FLIGHT);
    create_semaphore(grsemahpore, ldevice);

    std::vector<VkSemaphore> crsemahpore;
    crsemahpore.resize(constants::MAX_FRAMES_IN_FLIGHT);
    create_semaphore(crsemahpore, ldevice);

    fences.push_back(gifences);
    fences.push_back(cifences);
    semaphores.push_back(gisemahpore);
    semaphores.push_back(grsemahpore);
    semaphores.push_back(crsemahpore);

    // model
    frame->model.device = ldevice;
    frame->model.queue = queues[0];
    frame->model.pool = command_pool;
    frame->model.frame_index = 0;
    frame->model.fences = fences;
    frame->model.semaphores = semaphores;
    frame->model.swapchain = swapchain.buffer;
    frame->model.cmds = cmds;
    frame->model.renderpasses = renderpasses;
    frame->model.framebuffers = framebuffers;
    frame->model.extent = swapchain.extent;

    VDynamicState dynamic_state;
    dynamic_state.primitive_topology = true;
    dynamic_state.scissor = true;
    dynamic_state.viewport = true;

    VPipelineProperties line_material_properties;
    line_material_properties.topology = VK_PRIMITIVE_TOPOLOGY_LINE_LIST;
    line_pipeline.layout = pipeline_layout;
    VMaterial line_material;
    line_material.descriptor = descriptor;
    line_material.dynamic_states = dynamic_state;
    line_material.pipeline = line_pipeline;
    line_material.id = meshes[0].materialID;
    line_material.indexed = meshes[0].indexed;
    line_material.properties = line_material_properties;

    VPipelineProperties shape_material_properties;
    shape_material_properties.topology = VK_PRIMITIVE_TOPOLOGY_TRIANGLE_LIST;
    shape_pipeline.layout = pipeline_layout;
    VMaterial shape_material;
    shape_material.descriptor = descriptor;
    shape_material.dynamic_states = dynamic_state;
    shape_material.pipeline = shape_pipeline;
    shape_material.id = meshes[1].materialID;
    shape_material.indexed = meshes[1].indexed;
    shape_material.properties = shape_material_properties;

    VPipelineProperties particle_material_properties;
    particle_material_properties.topology = VK_PRIMITIVE_TOPOLOGY_POINT_LIST;
    particle_pipeline.layout = compute_pipeline_layout;
    VMaterial particle_material;
    particle_material.descriptor = compute_descriptor;
    particle_material.dynamic_states = dynamic_state;
    particle_material.pipeline = particle_pipeline;
    particle_material.id = 0;
    particle_material.indexed = false;
    particle_material.properties = particle_material_properties;
    
    particle_compute_pipeline.layout = compute_pipeline_layout;
    VMaterial particle_compute_material;
    particle_compute_material.descriptor = compute_descriptor;
    particle_compute_material.dynamic_states = dynamic_state;
    particle_compute_material.pipeline = particle_compute_pipeline;
    particle_compute_material.id = 0;
    particle_compute_material.indexed = false;
    particle_compute_material.properties = particle_material_properties;
    
    std::vector<VMaterial> materials{};
    materials.push_back(line_material);
    materials.push_back(shape_material);
    materials.push_back(particle_material);
    materials.push_back(particle_compute_material);
    frame->scene.materials = materials;

    std::vector<std::vector<VBuffer>> vertex_buffers;
    std::vector<VBuffer> index_buffers;
    for (int i = 0; i < meshes.size(); i++)
    {
        std::vector<VBuffer> vertex_buffer;
        VBuffer vbuffer;
        vbuffer.size = meshes[i].vertices.size();
        create_vertex_buffer(vbuffer, fixed_buffer_size, pdevice.pinfo.memoryProperties, ldevice);
        vertex_buffer.push_back(vbuffer);
        vertex_buffers.push_back(vertex_buffer);

        if (meshes[i].indices.size() > 0)
        {
            VBuffer ibuffer;
            ibuffer.size = meshes[i].indices.size();
            create_index_buffer(ibuffer, fixed_buffer_size, pdevice.pinfo.memoryProperties, ldevice);
            index_buffers.push_back(ibuffer);
        }
    }

    // copy scene data
    // lights
    uint32_t light_buffer_id = 1;
    std::vector<VBuffer> vb =  shader_buffers[light_buffer_id];
    copy_buffer_data<ogun::GPULight>(stage_buffer, shader_buffers[light_buffer_id], lights, 0, 0, scmd);
   
    // meshes
    for (int i = 0; i < meshes.size(); i++)
    {
        copy_buffer_data<sema::Vertex>(stage_buffer, vertex_buffers[i], meshes[i].vertices, 0, 0, scmd);
        if (meshes[i].indices.size() > 0)
        {
            copy_buffer_data<uint32_t>(stage_buffer, index_buffers, meshes[i].indices, 0, 0, scmd);
        }
    }

    // particles
    uint32_t particle__parameters_buffer_id = 0;
    uint32_t particle_buffer_id = 1;
    // std::vector<VBuffer> vb =  compute_shader_buffers[light_buffer_id];
    copy_buffer_data<ogun::GPUParticle>(stage_buffer, compute_shader_buffers[particle_buffer_id], particles, 0, 0, scmd);
    vertex_buffers.push_back(compute_shader_buffers[particle_buffer_id]);

    // scene
    ogun::GPUScene scene;
    scene.parameters.x = lights.size();
    scene.view = glm::vec4{cameras[0].position.x, cameras[0].position.y, cameras[0].position.z, 1.0f};
    frame->scene.scenes.push_back(scene);
    // frame->scene.cameras = cameras;
    frame->scene.vertex_buffers = vertex_buffers;
    frame->scene.index_buffers = index_buffers;
    frame->scene.shader_buffers = shader_buffers;
    frame->scene.primary_camera = cameras[0];
    frame->scene.particles = particles;
    frame->scene.stage_buffers = stage_buffers;
}

void draw_frame(float tick, VFrame* frame)
{
    uint32_t frame_index = frame->model.frame_index;

    /* compute commands */
    vkWaitForFences(frame->model.device, 1, &frame->model.fences[1][frame_index], VK_TRUE, UINT64_MAX);
    
    // data
    std::vector<std::vector<VBuffer>> scene_shader_buffers;
    scene_shader_buffers.push_back(frame->scene.shader_buffers[0]);
    scene_shader_buffers.push_back(frame->scene.shader_buffers[2]);
    scene_shader_buffers.push_back(frame->scene.shader_buffers[3]);
    update_shaders(tick, frame_index, scene_shader_buffers, frame->scene.primary_camera, frame->scene.scenes[0], frame->cursor);

    vkResetFences(frame->model.device, 1, &frame->model.fences[1][frame_index]);
    vkResetCommandBuffer(frame->model.cmds[1][frame_index], 0);

    // if (prepared[frame_index] == false)
    // {
    record_compute_commands(frame->model.cmds[1], frame_index, frame->model.renderpasses, frame->model.framebuffers, frame->model.extent, frame->scene);
    // }
        

    VkSubmitInfo submitInfo{};
    submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    submitInfo.commandBufferCount = 1;
    submitInfo.pCommandBuffers = &frame->model.cmds[1][frame_index];
    submitInfo.signalSemaphoreCount = 1;
    submitInfo.pSignalSemaphores = &frame->model.semaphores[1][frame_index];
    checkvk(vkQueueSubmit(frame->model.queue, 1, &submitInfo, frame->model.fences[1][frame_index]));

    // /* graphics commands */
    vkWaitForFences(frame->model.device, 1, &frame->model.fences[0][frame_index], VK_TRUE, UINT64_MAX);

    // // write headless compute data to local device buffer
    // // Make device writes visible to the host
    // void *mapped;
    // vkMapMemory(device, hostMemory, 0, VK_WHOLE_SIZE, 0, &mapped);
    // VkMappedMemoryRange mappedRange = vks::initializers::mappedMemoryRange();
    // mappedRange.memory = hostMemory;
    // mappedRange.offset = 0;
    // mappedRange.size = VK_WHOLE_SIZE;
    // vkInvalidateMappedMemoryRanges(device, 1, &mappedRange);
    // // Copy to output
    // memcpy(computeOutput.data(), mapped, bufferSize);
    // vkUnmapMemory(device, hostMemory);

    // record
    uint32_t image_index;
    VkResult result = vkAcquireNextImageKHR(frame->model.device, frame->model.swapchain, UINT64_MAX, frame->model.semaphores[0][frame_index], VK_NULL_HANDLE, &image_index);
    if (result == VK_ERROR_OUT_OF_DATE_KHR)
    {
        rebuild_swapchain(frame->window_extent);
        return;
    }
    assert(!(result != VK_SUCCESS && result != VK_SUBOPTIMAL_KHR));
    
    vkResetFences(frame->model.device, 1, &frame->model.fences[0][frame_index]);
    vkResetCommandBuffer(frame->model.cmds[0][frame_index], 0);
    
    // if (prepared[frame_index] == false)
    // {
    //     prepared[frame_index] = true;
    record_draw_commands(frame->model.cmds[0], frame_index, frame->model.renderpasses, frame->model.framebuffers, frame->model.extent, frame->scene, frame->passes_enabled);
    // }

    // submit
    std::vector<VkSemaphore> waitSemaphores;
    waitSemaphores.push_back(frame->model.semaphores[1][frame_index]);
    waitSemaphores.push_back(frame->model.semaphores[0][frame_index]);
    VkPipelineStageFlags waitStages[] = {VK_PIPELINE_STAGE_VERTEX_INPUT_BIT, VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT};
    
    std::vector<VkSemaphore> signalSemaphores;
    signalSemaphores.push_back(frame->model.semaphores[2][frame_index]);
    
    std::vector<VkSwapchainKHR> swapChains;
    swapChains.push_back(frame->model.swapchain);

    std::vector<VkCommandBuffer> submitBuffers;
    submitBuffers.push_back(frame->model.cmds[0][frame_index]);

    VkSubmitInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    create_info.pNext = NULL;
    create_info.waitSemaphoreCount = waitSemaphores.size();
    create_info.pWaitSemaphores = waitSemaphores.data();
    create_info.pWaitDstStageMask = waitStages;
    create_info.commandBufferCount = submitBuffers.size();
    create_info.pCommandBuffers = submitBuffers.data();
    create_info.signalSemaphoreCount = signalSemaphores.size();
    create_info.pSignalSemaphores = signalSemaphores.data();
    checkvk(vkQueueSubmit(frame->model.queue, 1, &create_info, frame->model.fences[0][frame_index]));

    /* present commands */
    VkPresentInfoKHR pcreate_info{};
    pcreate_info.sType = VK_STRUCTURE_TYPE_PRESENT_INFO_KHR;
    pcreate_info.pNext = NULL;
    pcreate_info.waitSemaphoreCount = signalSemaphores.size();
    pcreate_info.pWaitSemaphores = signalSemaphores.data();
    pcreate_info.swapchainCount = swapChains.size();
    pcreate_info.pSwapchains = swapChains.data();
    pcreate_info.pImageIndices = &image_index;
    result = vkQueuePresentKHR(frame->model.queue, &pcreate_info);
    if (result == VK_ERROR_OUT_OF_DATE_KHR || result == VK_SUBOPTIMAL_KHR || frame->resized)
    {
        frame->resized = false;
        rebuild_swapchain(frame->window_extent);
    }
    checkvk(result);

    // void* data;
    // frame->scene.images;
    // vkMapMemory(frame->model.device, frame->scene.images[1].memory, 0, frame->window_extent.width * frame->window_extent.height, 0, &data);
    // memcpy(data, frame->scene.images[1].img, (size_t)frame->window_extent.width * frame->window_extent.height);
    // vkUnmapMemory(frame->model.device, frame->scene.images[1].memory);
    VSingleCommand scmd;
    scmd.device = frame->model.device;
    scmd.queue = frame->model.queue;
    scmd.pool = frame->model.pool;
    // retrieve_texture_image(frame->scene.images[0], frame->window_extent, frame->scene.stage_buffers[0], scmd);

    // update index
    frame_index = (frame_index + 1) % constants::MAX_FRAMES_IN_FLIGHT;
    frame->model.frame_index = frame_index;
}

void retrieve_texture_image(VImage& image, VkExtent2D extent, VBuffer& stage_buffer, VSingleCommand scmd)
{
    VkDeviceSize size = extent.width * extent.height * 4 * sizeof(float);
    uint32_t mip_levels = static_cast<uint32_t>(std::floor(std::log2((std::max)(extent.width, extent.height)))) + 1;
    transition_image_layout(image.img, VK_IMAGE_LAYOUT_UNDEFINED, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, mip_levels, scmd);
    copy_image2buffer(image.img, stage_buffer.buffer, extent, scmd);
    const char* imagedata;
    vkMapMemory(scmd.device, stage_buffer.memory, 0, size, 0, (void**)&imagedata);
    for (int i = 0; i < extent.width; i++)
    {
        std::cout << "data " << imagedata[i] << std::endl;
    }
    memcpy((void*)imagedata, stage_buffer.data, static_cast<size_t>(size));
}

void hot_reload_shaders()
{

}

void translate_mesh(glm::vec3 transform, glm::vec3& transform_state)
{
    float movespeed =  0.001;
    glm::vec3 mspeed(movespeed);
    // if direction has changed, clear out previous model transform and move in new direction
    bool bflip = false;
    for (int i = 0; i < 3; i++)
    {
        int8_t sign = sgn(transform[i]);
        if (transform_state[i] != sign)
        {
            bflip = true;
        }
        transform_state[i] = sign;
    }

    // translate_object(current_active_object, transform*mspeed, bflip);
}

void translate_object(uint32_t object_index, glm::vec3 translation, bool bflip)
{
    // MeshBuffer* mbuffer = m_scene->meshbuffer();
    // glm::mat4 model = mbuffer->models()[object_index];
    // uint32_t numVertices = mbuffer->vsizes()[object_index];
    // uint32_t offset = mbuffer->offsets()[object_index];
    // std::vector<sema::Vertex> vertices;
    // vertices.resize(numVertices);

    // if (bflip)
    // {
    //     model = glm::mat4(1.0f);
    // }
    // else
    // {
    //     model = glm::translate(mbuffer->models()[object_index], translation);
    // }

    // mbuffer->updateModel(model, object_index);
    // uint32_t vindex = 0;
    // for (uint32_t v = offset; v < offset+numVertices; v++)
    // {
    //     glm::vec4 pos = mbuffer->models()[object_index] * glm::vec4(mbuffer->vertices()[v].position, 1.0f);
    //     vertices[vindex] = mbuffer->vertices()[v];
    //     vertices[vindex].position = glm::vec3(pos.x, pos.y, pos.z);
    //     mbuffer->updateVertex(vertices[vindex], v);
    //     vindex++;
    // }

    // uint32_t light_buffer_id = 1;
    // std::vector<VBuffer> vb =  shader_buffers[light_buffer_id];
    // copy_buffer_data<ogun::GPULight>(stage_buffer, shader_buffers[light_buffer_id], vertices, 0, 0, command_pool, ldevice, queue);
    // m_shader->updateVertexBuffer(vertices, object_index * sizeof(vertices[0])*vertices.size());
}

void rotate_mesh()
{

}

void scale_mesh()
{

}

void change_camera_perspective(ogun::VCamera& camera)
{
    if (camera.projection_mode == 0) { camera.projection_mode = 1; }
    else { camera.projection_mode = 0; }
}

void translate_camera(float angle, glm::vec3 axis, uint32_t type, ogun::VCamera& camera)
{
    if (type == 0)
    {
        camera.up += (axis*glm::vec3(angle * camera.speed * camera.speed_multiplier));
    }
    else if (type == 1)
    {    
        camera.position += (axis*glm::vec3(angle * camera.speed * camera.speed_multiplier));
    }
    else // if (type == 2)
    {
        camera.front += (axis*glm::vec3(angle * camera.speed * camera.speed_multiplier));
    }
}

void zoom_camera(ogun::VCamera& camera, float rotation)
{
    // camera_angle += angle;
    // camera_up += (axis*glm::vec3(angle * camera.speed * camera.speed_multiplier));
    // camera_up = glm::normalize(camera_up);
    camera.zoom_angle += glm::radians(rotation * camera.speed * camera.speed_multiplier);
}

void rotate_camera(ogun::VCamera& camera, float rotation, glm::vec3 axis)
{
    camera.model = glm::rotate(camera.model, rotation * camera.speed * camera.speed_multiplier, axis);
}

// void zoom_camera(uint32_t cameraID, float zoom)
// {
//     camera_zoom += zoom; // zoom multipler
// }

// void select_active_object(uint32_t objectID)
// {
//     uint32_t numObjectsInScene = m_scene->meshbuffer()->models().size();
//     active_object_id = (active_object_id + 1) % (numObjectsInScene-1);
// }

// void translate_active_object(glm::vec3 translation)
// {
//     float movespeed =  0.001;
//     glm::vec3 mspeed(movespeed);
//     bool bflip = false;
//     for (int i = 0; i < 3; i++)
//     {
//         int8_t sign = sgn(translation[i]);
//         if (active_object_index_transform[i] != sign)
//         {
//             bflip = true;
//         }
//         active_object_index_transform[i] = sign;
//     }
//     translateObject(active_object_id, transform * mspeed, bflip);
// }

// void translate_object(uint32_t objectID, glm::vec3 translation, bool bflip)
// {
//     MeshBuffer* mbuffer = m_scene->meshbuffer();
//     glm::mat4 model = mbuffer->models()[objectID];
//     uint32_t numVertices = mbuffer->vsizes()[objectID];
//     uint32_t offset = mbuffer->offsets()[objectID];
//     std::vector<sema::Vertex> vertices;
//     vertices.resize(numVertices);

//     if (bflip)
//     {
//         model = glm::mat4(1.0f);
//     }
//     else
//     {
//         model = glm::translate(mbuffer->models()[objectID], translation);
//     }
//     mbuffer->updateModel(model, objectID);
//     uint32_t vindex = 0;
//     for (uint32_t v = offset; v < offset+numVertices; v++)
//     {
//         glm::vec4 pos = mbuffer->models()[objectID] * glm::vec4(mbuffer->vertices()[v].position, 1.0f);
//         vertices[vindex] = mbuffer->vertices()[v];
//         vertices[vindex].position = glm::vec3(pos.x, pos.y, pos.z);
//         mbuffer->updateVertex(vertices[vindex], v);
//         vindex++;
//     }
    
//     update_vertex_buffer(vertices, objectID * sizeof(vertices[0])*vertices.size());
// }

void create_terrain(uint32_t id)
{
    // // terrain
    // // m_terrain->load_heightmap(terrainHeightMapExtent.x, terrainHeightMapExtent.y);
    // uint32_t terrain_quad_multiplier = 600u;
    // uint32_t terrain_width = 1u;
    // uint32_t terrain_height= 1u;
    // m_terrain->load_heightmap(terrain_quad_multiplier*terrain_width, terrain_quad_multiplier*terrain_height);
    // std::vector<TVertex> verts = m_terrain->vertices();
    // // std::vector<TVertex> verts = m_meshbuffer->vertices(); // = square1->vertices();
    // std::vector<uint16_t> inds = {0}; //m_meshbuffer->indices(); // = square1->indices();

}

}; //  namespace vulkan