/**
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_model.h"
#include "vulkan_shader.h"
#include <assert.h>
#include <vulkan/vulkan_win32.h>
#include <set>
#include <string>
#include <algorithm>
#include <array>
#include <stdexcept>
#include <iostream>
#include <chrono>

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

namespace vulkan
{

void create_instance(VkInstance& instance, std::vector<const char*> extensions, std::vector<const char*> layers)
{
    VkApplicationInfo appInfo;
    appInfo.pNext = NULL;
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "ogunEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 1, 0);
    appInfo.pEngineName = "ogunEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 1, 0);
    appInfo.apiVersion = VK_MAKE_API_VERSION(0, 1, 1, 0);

    VkInstanceCreateInfo create_info;
    create_info.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
    create_info.pNext = NULL;
    create_info.flags = 0;
    create_info.pApplicationInfo = &appInfo;
    create_info.enabledExtensionCount = extensions.size();
    create_info.ppEnabledExtensionNames = extensions.data();
    create_info.enabledLayerCount = layers.size();
    create_info.ppEnabledLayerNames = layers.data();
    
    checkvk(vkCreateInstance(&create_info,
        nullptr,
        &instance));
}

void create_debugger()
{}

void create_surface_win32(VkSurfaceKHR& surface, VkInstance instance, HWND hwnd)
{
    VkWin32SurfaceCreateInfoKHR create_info = {};
    create_info.sType = VK_STRUCTURE_TYPE_WIN32_SURFACE_CREATE_INFO_KHR;
    create_info.pNext = NULL;
    create_info.flags = 0;
    create_info.hwnd = hwnd;
    create_info.hinstance = GetModuleHandle(nullptr);
    checkvk(vkCreateWin32SurfaceKHR(instance,
                                        &create_info,
                                        nullptr,
                                        &surface));
}

void create_physical_device(PDevice& pdevice, VkInstance instance, VkSurfaceKHR surface)
{
    std::vector<VkPhysicalDevice> pdevices;
    uint32_t pdevicesCount;
    vkEnumeratePhysicalDevices(instance, &pdevicesCount, nullptr);
    pdevices.resize(pdevicesCount);
    vkEnumeratePhysicalDevices(instance, &pdevicesCount, pdevices.data());

    // Pick most suitable physical device from list
    uint32_t max_device_rating = 0;
    uint32_t rating;
    bool pdevice_found = false;
    for (auto& device : pdevices)
    {
        PDeviceInfo pinfo;
        std::vector<VkDeviceQueueCreateInfo> qinfo;
        query_pdevice_info(device, surface, &pinfo);
        query_pdevice_queue_info(device, surface, pinfo.queueFamiliesProperties, qinfo);
        rating = rate_pdevice(pinfo, qinfo);
        if (rating > max_device_rating)
        {
            max_device_rating = rating;
            pdevice.device = device;
            pdevice.pinfo = pinfo;
            pdevice.qinfo = qinfo;
            pdevice_found = true;
        }
    }
    assert(pdevice_found);
}

void create_logical_device(VkDevice& ldevice, std::vector<VkQueue>& queues, VkPhysicalDevice pdevice, VkPhysicalDeviceFeatures features, std::vector<VkDeviceQueueCreateInfo> queue_info, std::vector<const char*> extensions)
{
    VkPhysicalDeviceFeatures2 supported_features{};
    VkPhysicalDeviceVulkan11Features extra_features{};
    supported_features.sType = VK_STRUCTURE_TYPE_PHYSICAL_DEVICE_FEATURES_2;
    supported_features.pNext = &extra_features;
    vkGetPhysicalDeviceFeatures2(pdevice, &supported_features);

    VkDeviceCreateInfo create_info = {};
    create_info.sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO;
    create_info.pNext = NULL;
    create_info.flags = 0;
    create_info.queueCreateInfoCount = queue_info.size();
    create_info.pQueueCreateInfos = queue_info.data();
    create_info.ppEnabledLayerNames = NULL;
    create_info.enabledLayerCount = 0;
    create_info.ppEnabledExtensionNames = extensions.data();
    create_info.enabledExtensionCount = extensions.size();
    create_info.pEnabledFeatures = NULL;
    create_info.pEnabledFeatures = &features;

    checkvk(vkCreateDevice(pdevice,
                            &create_info,
                            nullptr,
                            &ldevice));

    
    queues.resize(queue_info.size());
    uint32_t qindex = 0;
    for (auto qinfo : queue_info)
    {
        vkGetDeviceQueue(ldevice, qinfo.queueFamilyIndex, qindex, &queues[qinfo.queueFamilyIndex]);
        assert(queues[qinfo.queueFamilyIndex] != NULL);
    }
}

void create_swapchain(PSwapchain& swapchain, PSwapchainInfo info, VkDevice device, VkSurfaceKHR surface)
{
    uint32_t image_count = 0;
    uint32_t image_array_layers = 1;
    VkImageUsageFlags image_usage = VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT;
    VkSharingMode image_sharing_mode = VK_SHARING_MODE_EXCLUSIVE;
    VkCompositeAlphaFlagBitsKHR composite_alpha = VK_COMPOSITE_ALPHA_OPAQUE_BIT_KHR;
    VkBool32 isClipped = VK_TRUE;
    VkSwapchainKHR oldswapchain = VK_NULL_HANDLE;
    VkSurfaceFormatKHR surface_format = select_swapchain_surface_format(info.formats);
    VkPresentModeKHR present_mode = select_swapchain_present_modes(info.present_modes);
    VkExtent2D swapchain_extent = select_swapchain_extent(info.capabilities, info.extent);

    if (info.capabilities.minImageCount + 1 == constants::MAX_FRAMES_IN_FLIGHT)
    {
        image_count = info.capabilities.minImageCount + 1;
    }
    else
    {
        image_count = constants::MAX_FRAMES_IN_FLIGHT;
    }
   
    if (info.capabilities.maxImageCount > 0 && image_count > info.capabilities.maxImageCount)
    {
        image_count = info.capabilities.maxImageCount;
    }

    VkSwapchainCreateInfoKHR create_info = {};
    create_info.sType = VK_STRUCTURE_TYPE_SWAPCHAIN_CREATE_INFO_KHR;
    create_info.pNext = NULL;
    create_info.flags = 0;
    create_info.surface = surface;
    create_info.minImageCount = image_count;
    create_info.imageFormat = surface_format.format;
    create_info.imageColorSpace = surface_format.colorSpace;
    create_info.imageExtent = swapchain_extent;
    create_info.imageArrayLayers = image_array_layers;
    create_info.imageUsage = image_usage;
    create_info.imageSharingMode = image_sharing_mode;
    create_info.queueFamilyIndexCount = 0;
    create_info.pQueueFamilyIndices = NULL;
    create_info.preTransform = info.capabilities.currentTransform;;
    create_info.compositeAlpha = composite_alpha;
    create_info.presentMode = present_mode;
    create_info.clipped = isClipped;
    create_info.oldSwapchain = oldswapchain;
    
    checkvk(vkCreateSwapchainKHR(device,
                                 &create_info,
                                 nullptr,
                                 &swapchain.buffer));

    uint32_t swapchain_imageCount;
    std::vector<VkImage> swapchain_images;
    vkGetSwapchainImagesKHR(device, swapchain.buffer, &swapchain_imageCount, nullptr);
    swapchain_images.resize(swapchain_imageCount);
    vkGetSwapchainImagesKHR(device, swapchain.buffer, &swapchain_imageCount, swapchain_images.data());
    swapchain.views.resize(swapchain_images.size());
    create_imageview(swapchain.views, device, swapchain_images, surface_format.format, VK_IMAGE_ASPECT_COLOR_BIT, 1u);
    swapchain.format = surface_format.format;
    swapchain.extent = swapchain_extent;
}

void create_renderpass(VkRenderPass& renderpass, VkDevice device, VRenderpassInfo info)
{
    /* attachments */
    std::vector<VkAttachmentDescription> attachments;
    VkAttachmentDescription colorAttachment{};
    colorAttachment.format = info.iformat;
    colorAttachment.samples = info.msaa_samples;
    colorAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
    colorAttachment.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
    colorAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
    colorAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
    colorAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    colorAttachment.finalLayout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;
    attachments.push_back(colorAttachment);
    
    uint32_t attachment_index = 0u;

    VkAttachmentReference colorAttachmentRef{};
    colorAttachmentRef.attachment = attachment_index;
    attachment_index++;
    colorAttachmentRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;

    std::vector<VkAttachmentReference> colorAttachments;
    colorAttachments.push_back(colorAttachmentRef);

    VkAttachmentReference depthStencilAttachmentRef{};
    if (info.hasAttachments[0] == true)
    {
        VkAttachmentDescription depthStencilAttachment{};
        depthStencilAttachment.format = info.dformat;
        depthStencilAttachment.samples = info.msaa_samples;
        depthStencilAttachment.loadOp = VK_ATTACHMENT_LOAD_OP_CLEAR;
        depthStencilAttachment.storeOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
        depthStencilAttachment.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
        depthStencilAttachment.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
        depthStencilAttachment.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
        depthStencilAttachment.finalLayout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;
        attachments.push_back(depthStencilAttachment);
    
        depthStencilAttachmentRef.attachment = attachment_index;
        attachment_index++;
        depthStencilAttachmentRef.layout = VK_IMAGE_LAYOUT_DEPTH_STENCIL_ATTACHMENT_OPTIMAL;
    }

    VkAttachmentReference colorAttachmentResolveRef{};
    if (info.hasAttachments[1] == true)
    {
        VkAttachmentDescription colorAttachmentResolve{};
        colorAttachmentResolve.format = info.iformat;
        colorAttachmentResolve.samples = VK_SAMPLE_COUNT_1_BIT;
        colorAttachmentResolve.loadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
        colorAttachmentResolve.storeOp = VK_ATTACHMENT_STORE_OP_STORE;
        colorAttachmentResolve.stencilLoadOp = VK_ATTACHMENT_LOAD_OP_DONT_CARE;
        colorAttachmentResolve.stencilStoreOp = VK_ATTACHMENT_STORE_OP_DONT_CARE;
        colorAttachmentResolve.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
        colorAttachmentResolve.finalLayout = VK_IMAGE_LAYOUT_PRESENT_SRC_KHR;
        attachments.push_back(colorAttachmentResolve);

        colorAttachmentResolveRef.attachment = attachment_index;
        colorAttachmentResolveRef.layout = VK_IMAGE_LAYOUT_COLOR_ATTACHMENT_OPTIMAL;
    }

    VkSubpassDescription subpass{};
    subpass.pipelineBindPoint = info.bpoint;
    subpass.colorAttachmentCount = colorAttachments.size();
    subpass.pColorAttachments = colorAttachments.data();
    subpass.pDepthStencilAttachment = (info.hasAttachments[0] == true) ? &depthStencilAttachmentRef : NULL;
    subpass.pResolveAttachments = (info.hasAttachments[1] == true) ? &colorAttachmentResolveRef : NULL;
    subpass.pPreserveAttachments = NULL;

    std::vector<VkSubpassDescription> subpasses;
    subpasses.push_back(subpass);

    /* dependencies */
    VkSubpassDependency dependency{};
    dependency.srcSubpass = VK_SUBPASS_EXTERNAL;
    dependency.dstSubpass = 0u;
    dependency.srcStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_LATE_FRAGMENT_TESTS_BIT;
    dependency.srcAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    dependency.dstStageMask = VK_PIPELINE_STAGE_COLOR_ATTACHMENT_OUTPUT_BIT | VK_PIPELINE_STAGE_EARLY_FRAGMENT_TESTS_BIT;
    dependency.dstAccessMask = VK_ACCESS_COLOR_ATTACHMENT_WRITE_BIT | VK_ACCESS_DEPTH_STENCIL_ATTACHMENT_WRITE_BIT;
    
    std::vector<VkSubpassDependency> dependencies;
    dependencies.push_back(dependency);

    VkRenderPassCreateInfo create_info;
    create_info.sType = VK_STRUCTURE_TYPE_RENDER_PASS_CREATE_INFO;
    create_info.pNext = NULL;
    create_info.flags = 0u;
    create_info.attachmentCount = static_cast<uint32_t>(attachments.size());
    create_info.pAttachments = attachments.data();
    create_info.subpassCount = subpasses.size();
    create_info.pSubpasses = subpasses.data();
    create_info.dependencyCount = dependencies.size();
    create_info.pDependencies = dependencies.data();

    checkvk(vkCreateRenderPass(device,
        &create_info,
            nullptr,
        &renderpass));
}

void create_fence(std::vector<VkFence>& fences, VkFenceCreateFlagBits flags, VkDevice device)
{
    VkFenceCreateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
    create_info.flags = flags;
    for (uint32_t i = 0; i < fences.size(); i++)
    {
        checkvk(vkCreateFence(device, &create_info, nullptr, &fences[i]));
    }
}

void create_semaphore(std::vector<VkSemaphore>& semaphores, VkDevice device)
{
    VkSemaphoreCreateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_SEMAPHORE_CREATE_INFO;
    for (uint32_t i = 0; i < semaphores.size(); i++)
    {
        checkvk(vkCreateSemaphore(device, &create_info, nullptr, &semaphores[i]));
    }
}

void create_command_pool(VkCommandPool& command_pool, VkDevice device, std::optional<uint32_t> gindex)
{
    VkCommandPoolCreateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
    create_info.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
    create_info.queueFamilyIndex = gindex.value();
    checkvk(vkCreateCommandPool(device,
                                &create_info,
                                nullptr,
                                &command_pool));
}

void create_command_buffer(std::vector<VkCommandBuffer>& command_buffers, VkDevice device, VkCommandPool pool)
{
    VkCommandBufferAllocateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    create_info.commandPool = pool;
    create_info.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    create_info.commandBufferCount = (uint32_t) command_buffers.size();
    checkvk(vkAllocateCommandBuffers(device,
                                     &create_info,
                                     command_buffers.data()));
}

void create_pipeline_layout(VkPipelineLayout& layout, std::vector<VkDescriptorSetLayout> descriptor_layouts, VkDevice device)
{
    // VkPushConstantRange push_constant;
    // push_constant.offset = 0;
    // push_constant.size = sizeof(ogun::GPUMeshInfo);
    // push_constant.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;

    std::vector<VkPushConstantRange> push_constants;
    // push_constants.push_back(push_constant);

    VkPipelineLayoutCreateInfo pcreate_info{};
    pcreate_info.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
    pcreate_info.pNext = NULL;
    pcreate_info.flags = 0u;
    pcreate_info.setLayoutCount = descriptor_layouts.size();
    pcreate_info.pSetLayouts = descriptor_layouts.data();
    pcreate_info.pushConstantRangeCount = push_constants.size();
    pcreate_info.pPushConstantRanges = push_constants.data();
    checkvk(vkCreatePipelineLayout(device,
        &pcreate_info,
        nullptr,
        &layout));
}


void create_raytracing_pipeline(VPipeline& pipeline, VkPipelineLayout pipeline_layout, std::vector<VShaderModule> shaders, VkDevice device)
{
    // VkRayTracingPipelineCreateInfoKHR
    // VkStructureType                                      sType;
    // const void*                                          pNext;
    // VkPipelineCreateFlags                                flags;
    // uint32_t                                             stageCount;
    // const VkPipelineShaderStageCreateInfo*               pStages;
    // uint32_t                                             groupCount;
    // const VkRayTracingShaderGroupCreateInfoKHR*          pGroups;
    // uint32_t                                             maxPipelineRayRecursionDepth;
    // const VkPipelineLibraryCreateInfoKHR*                pLibraryInfo;
    // const VkRayTracingPipelineInterfaceCreateInfoKHR*    pLibraryInterface;
    // const VkPipelineDynamicStateCreateInfo*              pDynamicState;
    // VkPipelineLayout                                     layout;
    // VkPipeline                                           basePipelineHandle;
    // int32_t                                              basePipelineIndex;
    
    // vkCreateRayTracingPipelinesKHR
    // VkDevice                                    device,
    // VkDeferredOperationKHR                      deferredOperation,
    // VkPipelineCache                             pipelineCache,
    // uint32_t                                    createInfoCount,
    // const VkRayTracingPipelineCreateInfoKHR*    pCreateInfos,
    // const VkAllocationCallbacks*                pAllocator,
    // VkPipeline*                                 pPipelines

    VkRayTracingPipelineCreateInfoKHR create_info{};
    // create_info.sType = 0;
    // create_info.pNext = 0;
    // create_info.flags = 0;
    // create_info.stageCount = 0;
    // create_info.pStages = 0;
    // create_info.groupCount = 0;
    // create_info.pGroups = 0;
    // create_info.maxPipelineRayRecursionDepth = 0;
    // create_info.pLibraryInfo = 0;
    // create_info.pLibraryInterface = 0;
    // create_info.pDynamicState = 0;
    // create_info.layout = 0;
    // create_info.basePipelineHandle = 0;
    // create_info.basePipelineIndex = 0;
    // checkvk(vkCreateRayTracingPipelinesKHR(device, VK_NULL_HANDLE, 1, &create_info, nullptr, &piFpeline.pipeline));
    pipeline.bpoint = VK_PIPELINE_BIND_POINT_RAY_TRACING_KHR;
}

void create_compute_pipeline(VPipeline& pipeline, VkPipelineLayout pipeline_layout, std::vector<VShaderModule> shaders, VkDevice device)
{
    VkPipelineShaderStageCreateInfo screate_info{};
    screate_info.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
    screate_info.pNext = NULL;
    screate_info.flags = 0u;
    screate_info.stage = shaders[0].stage;
    screate_info.module = shaders[0].module;
    screate_info.pName = shaders[0].entry_name;

    VkComputePipelineCreateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
    create_info.pNext = NULL;
    create_info.flags = 0u;
    create_info.layout = pipeline_layout;
    create_info.stage = screate_info;
    create_info.basePipelineHandle = VK_NULL_HANDLE;
    create_info.basePipelineIndex = 0;
    checkvk(vkCreateComputePipelines(device, VK_NULL_HANDLE, 1, &create_info, nullptr, &pipeline.pipeline));
    pipeline.bpoint = VK_PIPELINE_BIND_POINT_COMPUTE;
}

void create_graphics_pipeline(VPipeline& pipeline, VPipelineInfo info, VkDevice device, VkRenderPass renderpass, VkPipelineLayout pipeline_layout, std::vector<VShaderModule> shaders, sema::VertexType vertex_type)
{
    std::vector<VkVertexInputBindingDescription> bindingDescription;
    std::vector<VkVertexInputAttributeDescription> attributeDescriptions;
    if (vertex_type == sema::VertexType::MESH)
    {
        bindingDescription = vertex_binding();
        attributeDescriptions = vertex_attribute();
    }
    else if (vertex_type == sema::VertexType::PARTICLE)
    {
        bindingDescription = particle_vertex_binding();
        attributeDescriptions = particle_vertex_attribute();
    }

    VkPipelineVertexInputStateCreateInfo vertex_input_info{};
    vertex_input_info.sType = VK_STRUCTURE_TYPE_PIPELINE_VERTEX_INPUT_STATE_CREATE_INFO;
    vertex_input_info.pNext = NULL;
    vertex_input_info.flags = 0u;
    vertex_input_info.pVertexBindingDescriptions = bindingDescription.data();
    vertex_input_info.vertexBindingDescriptionCount = static_cast<uint32_t>(bindingDescription.size());
    vertex_input_info.pVertexAttributeDescriptions = attributeDescriptions.data();
    vertex_input_info.vertexAttributeDescriptionCount = static_cast<uint32_t>(attributeDescriptions.size());

    VkPipelineInputAssemblyStateCreateInfo input_assembly{};
    input_assembly.sType = VK_STRUCTURE_TYPE_PIPELINE_INPUT_ASSEMBLY_STATE_CREATE_INFO;
    input_assembly.pNext = NULL;
    input_assembly.flags = 0u;
    input_assembly.topology = info.topology;
    input_assembly.primitiveRestartEnable = VK_FALSE;

    VkPipelineViewportStateCreateInfo viewport_state{};
    viewport_state.sType = VK_STRUCTURE_TYPE_PIPELINE_VIEWPORT_STATE_CREATE_INFO;
    viewport_state.viewportCount = 1;
    viewport_state.pViewports;
    viewport_state.scissorCount = 1;
    viewport_state.pScissors;

    VkPipelineRasterizationStateCreateInfo rasterizer{};
    rasterizer.sType = VK_STRUCTURE_TYPE_PIPELINE_RASTERIZATION_STATE_CREATE_INFO;
    rasterizer.pNext = NULL;
    rasterizer.flags = 0u;
    rasterizer.depthClampEnable = VK_FALSE;
    rasterizer.rasterizerDiscardEnable = VK_FALSE;
    rasterizer.polygonMode = info.pmode;
    rasterizer.lineWidth = 1.0f;
    rasterizer.cullMode = VK_CULL_MODE_BACK_BIT;
    rasterizer.frontFace = VK_FRONT_FACE_COUNTER_CLOCKWISE;
    rasterizer.depthBiasEnable = VK_FALSE;
    rasterizer.depthBiasConstantFactor = 0.0f;
    rasterizer.depthBiasClamp = 0.0f;
    rasterizer.depthBiasSlopeFactor = 0.0f;

    VkPipelineMultisampleStateCreateInfo multisampling{};
    multisampling.sType = VK_STRUCTURE_TYPE_PIPELINE_MULTISAMPLE_STATE_CREATE_INFO;
    multisampling.pNext = NULL;
    multisampling.flags = 0u;
    multisampling.sampleShadingEnable = VK_FALSE;
    multisampling.rasterizationSamples = info.samples;
    multisampling.minSampleShading = 1.0f;
    multisampling.pSampleMask = nullptr;
    multisampling.alphaToCoverageEnable = VK_FALSE;
    multisampling.alphaToOneEnable = VK_FALSE;

    VkStencilOpState stencilFront;
    stencilFront.failOp = VK_STENCIL_OP_ZERO;
    stencilFront.passOp = VK_STENCIL_OP_ZERO;
    stencilFront.depthFailOp = VK_STENCIL_OP_ZERO;
    stencilFront.compareOp = VK_COMPARE_OP_ALWAYS;
    stencilFront.compareMask = 0xFf;
    stencilFront.writeMask = 0xfF;
    stencilFront.reference = 1;

    VkStencilOpState stencilBack;
    stencilBack.failOp = VK_STENCIL_OP_ZERO;
    stencilBack.passOp = VK_STENCIL_OP_ZERO;
    stencilBack.depthFailOp = VK_STENCIL_OP_ZERO;
    stencilBack.compareOp = VK_COMPARE_OP_ALWAYS;
    stencilBack.compareMask = 0xFF;
    stencilBack.writeMask =  0xFF;
    stencilBack.reference = 1;

    VkPipelineDepthStencilStateCreateInfo depth_stencil;
    depth_stencil.sType = VK_STRUCTURE_TYPE_PIPELINE_DEPTH_STENCIL_STATE_CREATE_INFO;
    depth_stencil.pNext = NULL;
    depth_stencil.flags = 0u;
    depth_stencil.depthTestEnable = VK_TRUE;
    depth_stencil.depthWriteEnable = VK_TRUE;
    depth_stencil.depthCompareOp = VK_COMPARE_OP_LESS;
    depth_stencil.depthBoundsTestEnable = VK_TRUE;
    depth_stencil.minDepthBounds = 0.0f;
    depth_stencil.maxDepthBounds = 1.0f;
    depth_stencil.stencilTestEnable = VK_FALSE;
    depth_stencil.front = {};
    depth_stencil.back = {};

    VkPipelineColorBlendAttachmentState color_blend_attachment{};
    color_blend_attachment.colorWriteMask = VK_COLOR_COMPONENT_R_BIT | VK_COLOR_COMPONENT_G_BIT | VK_COLOR_COMPONENT_B_BIT | VK_COLOR_COMPONENT_A_BIT;
    color_blend_attachment.blendEnable = VK_FALSE;
    color_blend_attachment.srcColorBlendFactor = VK_BLEND_FACTOR_ONE;
    color_blend_attachment.dstColorBlendFactor = VK_BLEND_FACTOR_ZERO;
    color_blend_attachment.colorBlendOp = VK_BLEND_OP_ADD;
    color_blend_attachment.srcAlphaBlendFactor = VK_BLEND_FACTOR_ONE; 
    color_blend_attachment.dstAlphaBlendFactor = VK_BLEND_FACTOR_ZERO;
    color_blend_attachment.alphaBlendOp = VK_BLEND_OP_ADD;

    VkPipelineColorBlendStateCreateInfo color_blending{};
    color_blending.sType = VK_STRUCTURE_TYPE_PIPELINE_COLOR_BLEND_STATE_CREATE_INFO;
    color_blending.pNext = NULL;
    color_blending.flags = 0u;
    color_blending.logicOpEnable = VK_FALSE;
    color_blending.logicOp = VK_LOGIC_OP_COPY;
    color_blending.attachmentCount = 1u;
    color_blending.pAttachments = &color_blend_attachment;
    color_blending.blendConstants[0] = 0.0f;
    color_blending.blendConstants[1] = 0.0f;
    color_blending.blendConstants[2] = 0.0f;
    color_blending.blendConstants[3] = 0.0f;


    std::vector<VkPipelineShaderStageCreateInfo> shader_stages;
    for (int i=0; i<shaders.size(); i++)
    {
        VkPipelineShaderStageCreateInfo screate_info{};
        screate_info.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
        screate_info.pNext = NULL;
        screate_info.flags = 0u;
        screate_info.stage = shaders[i].stage;
        screate_info.module = shaders[i].module;
        screate_info.pName = shaders[i].entry_name;
        shader_stages.push_back(screate_info);
    }

    VkPipelineDynamicStateCreateInfo dynamics_state{};
    dynamics_state.sType = VK_STRUCTURE_TYPE_PIPELINE_DYNAMIC_STATE_CREATE_INFO;
    dynamics_state.pNext = NULL;
    dynamics_state.flags = 0u;
    dynamics_state.dynamicStateCount = static_cast<uint32_t>(info.dynamics_states.size());
    dynamics_state.pDynamicStates = info.dynamics_states.data();

    uint32_t subpass = 0u;
    VkPipelineCache pipeline_cache = NULL;
    VkGraphicsPipelineCreateInfo create_info;
    VkPipeline base_pipeline_handle = VK_NULL_HANDLE;
    uint32_t base_pipeline_index = 0u;
    create_info.sType = VK_STRUCTURE_TYPE_GRAPHICS_PIPELINE_CREATE_INFO;
    create_info.pNext = NULL;
    create_info.flags = 0u;
    create_info.stageCount = shader_stages.size();
    create_info.pStages = shader_stages.data();
    create_info.pVertexInputState = &vertex_input_info;
    create_info.pInputAssemblyState = &input_assembly;
    create_info.pViewportState = &viewport_state;
    create_info.pRasterizationState = &rasterizer;
    create_info.pMultisampleState = &multisampling;
    create_info.pDepthStencilState = &depth_stencil;
    create_info.pColorBlendState = &color_blending;
    create_info.pDynamicState = &dynamics_state;
    create_info.layout = pipeline_layout;
    create_info.renderPass = renderpass;
    create_info.subpass = subpass;
    create_info.basePipelineHandle = base_pipeline_handle;
    create_info.basePipelineIndex = base_pipeline_index;
    create_info.pTessellationState = NULL;
    std::vector<VkGraphicsPipelineCreateInfo> create_infos;
    std::vector<VkPipeline> pipelines;
    create_infos.push_back(create_info);
    pipelines.push_back(pipeline.pipeline);
    checkvk(vkCreateGraphicsPipelines(device,
                                       pipeline_cache,
                                       create_infos.size(),
                                       create_infos.data(),
                                       nullptr,
                                       &pipeline.pipeline));
    pipeline.bpoint = VK_PIPELINE_BIND_POINT_GRAPHICS;
}

void create_shader_module(VkShaderModule& shader, VkDevice device, const std::string& filename)
{
    auto shaderCode = readFile(filename);
    VkShaderModuleCreateInfo create_info;
    create_info.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
    create_info.pNext = NULL;
    create_info.flags = 0;
    create_info.codeSize =  shaderCode.size();
    create_info.pCode = reinterpret_cast<const uint32_t*>(shaderCode.data());
    checkvk(vkCreateShaderModule(device,
                                 &create_info,
                                 nullptr,
                                 &shader));
}

void create_descriptor_layout(VkDescriptorSetLayout& layout, VkDevice device, std::vector<VkDescriptorSetLayoutBinding> bindings)
{
    VkDescriptorSetLayoutCreateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
    create_info.flags = 0;
    create_info.pNext = nullptr;
    create_info.bindingCount = bindings.size();
    create_info.pBindings = bindings.data();
    checkvk(vkCreateDescriptorSetLayout(device,
                                            &create_info,
                                            nullptr,
                                            &layout));
}

void create_compute_descriptor(VDescriptor& descriptor, std::vector<std::vector<VBuffer>>& shader_buffers, std::vector<VkDescriptorImageInfo> textures, VkDevice device, VkPhysicalDeviceMemoryProperties mproperties)
{
    uint32_t set_size = constants::MAX_FRAMES_IN_FLIGHT;

    // buffers
    std::vector<VBuffer> ubo_buffers;
    uint32_t ubo_size = sizeof(ogun::GPUParticlesParameters);
    VkDescriptorType ubo_descriptor_type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    uint32_t ubo_binding_id = 0;
    ubo_buffers.resize(set_size);
    create_uniform_buffer(ubo_buffers, ubo_size, mproperties, device);
    shader_buffers.push_back(ubo_buffers);

    std::vector<VBuffer> particle_buffers;
    uint32_t particle_size = sizeof(ogun::GPUParticle) * ogun::PARTICLE_COUNT;
    VkDescriptorType particle_descriptor_type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    uint32_t particle_binding_id = 1;
    particle_buffers.resize(set_size);
    create_storage_buffer(particle_buffers, particle_size, mproperties, device);
    shader_buffers.push_back(particle_buffers);
    
    // pools
    VkDescriptorPoolSize ubo_pool;
    ubo_pool.type = ubo_descriptor_type;
    ubo_pool.descriptorCount = static_cast<uint32_t>(set_size);

    VkDescriptorPoolSize particle_pool;
    particle_pool.type = particle_descriptor_type;
    particle_pool.descriptorCount = static_cast<uint32_t>(set_size) * 2;

    std::vector<VkDescriptorPoolSize> pools;
    pools.push_back(ubo_pool);
    pools.push_back(particle_pool);

    VkDescriptorPool descriptor_pool;
    VkDescriptorPoolCreateInfo pcreate_info{};
    pcreate_info.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
    pcreate_info.poolSizeCount = pools.size();
    pcreate_info.pPoolSizes = pools.data();
    pcreate_info.maxSets = static_cast<uint32_t>(set_size);
    checkvk(vkCreateDescriptorPool(device, &pcreate_info, nullptr, &descriptor_pool));

    // layouts
    VkDescriptorSetLayoutBinding ubo_binding{};
    ubo_binding.binding = ubo_binding_id;
    ubo_binding.descriptorCount = 1;
    ubo_binding.descriptorType = ubo_descriptor_type;
    ubo_binding.pImmutableSamplers = nullptr;
    ubo_binding.stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
    
    VkDescriptorSetLayoutBinding particlein_binding{};
    particlein_binding.binding = 1;
    particlein_binding.descriptorCount = 1;
    particlein_binding.descriptorType = particle_descriptor_type;
    particlein_binding.pImmutableSamplers = nullptr;
    particlein_binding.stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;

    VkDescriptorSetLayoutBinding particleout_binding{};
    particleout_binding.binding = 2;
    particleout_binding.descriptorCount = 1;
    particleout_binding.descriptorType = particle_descriptor_type;
    particleout_binding.pImmutableSamplers = nullptr;
    particleout_binding.stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;

    std::vector<VkDescriptorSetLayoutBinding> uniform_bindings;
    uniform_bindings.push_back(ubo_binding);
    uniform_bindings.push_back(particlein_binding);
    uniform_bindings.push_back(particleout_binding);

    VkDescriptorSetLayout descriptor_layout;
    VkDescriptorSetLayoutCreateInfo layout_info{};
    layout_info.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
    layout_info.flags = 0;
    layout_info.pNext = nullptr;
    layout_info.bindingCount = uniform_bindings.size();
    layout_info.pBindings = uniform_bindings.data();
    checkvk(vkCreateDescriptorSetLayout(device,
        &layout_info,
        nullptr,
        &descriptor_layout));

    // sets
    std::vector<VkDescriptorSet> descriptor_set;
    std::vector<VkDescriptorSetLayout> layouts(set_size, descriptor_layout);
    VkDescriptorSetAllocateInfo dcreate_info{};
    dcreate_info.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    dcreate_info.descriptorPool = descriptor_pool;
    dcreate_info.descriptorSetCount = static_cast<uint32_t>(set_size);
    dcreate_info.pSetLayouts = layouts.data();
    descriptor_set.resize(set_size);
    checkvk(vkAllocateDescriptorSets(device,
                                    &dcreate_info,
                                    descriptor_set.data()));
                                
    std::vector<VkWriteDescriptorSet> writes;
    for (size_t i = 0; i < set_size; i++) 
    {
        VkDescriptorBufferInfo ubo_write_info{};
        ubo_write_info.buffer = ubo_buffers[i].buffer;
        ubo_write_info.offset = 0;
        ubo_write_info.range = ubo_size;
    
        VkWriteDescriptorSet ubo_write;
        ubo_write.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        ubo_write.pNext = NULL;
        ubo_write.dstSet = descriptor_set[i];
        ubo_write.dstBinding = ubo_binding_id;
        ubo_write.dstArrayElement = 0;
        ubo_write.descriptorType = ubo_descriptor_type;
        ubo_write.descriptorCount = 1;
        ubo_write.pBufferInfo = &ubo_write_info;
        ubo_write.pImageInfo = 0;

        VkDescriptorBufferInfo pi_write_info{};
        pi_write_info.buffer = particle_buffers[(i - 1) % set_size].buffer;
        pi_write_info.offset = 0;
        pi_write_info.range = particle_size;
        
        VkWriteDescriptorSet pi_write;
        pi_write.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        pi_write.pNext = NULL;
        pi_write.dstSet = descriptor_set[i];
        pi_write.dstBinding = 1;
        pi_write.dstArrayElement = 0;
        pi_write.descriptorType = particle_descriptor_type;
        pi_write.descriptorCount = 1;
        pi_write.pBufferInfo = &pi_write_info;
        pi_write.pImageInfo = 0;
        
        VkDescriptorBufferInfo po_write_info{};
        po_write_info.buffer = particle_buffers[i].buffer;
        po_write_info.offset = 0;
        po_write_info.range = particle_size;
        
        VkWriteDescriptorSet po_write;
        po_write.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        po_write.pNext = NULL;
        po_write.dstSet = descriptor_set[i];
        po_write.dstBinding = 2;
        po_write.dstArrayElement = 0;
        po_write.descriptorType = particle_descriptor_type;
        po_write.descriptorCount = 1;
        po_write.pBufferInfo = &po_write_info;
        po_write.pImageInfo = 0;

        writes = {};
        writes.push_back(ubo_write);
        writes.push_back(pi_write);
        writes.push_back(po_write);
        vkUpdateDescriptorSets(device, writes.size(), writes.data(), 0, nullptr);
    }

    descriptor.sets = descriptor_set;
    descriptor.layout = descriptor_layout;
}

void create_descriptor(VDescriptor& descriptor, std::vector<std::vector<VBuffer>>& shader_buffers, std::vector<VkDescriptorImageInfo> textures, VkDevice device, VkPhysicalDeviceMemoryProperties mproperties)
{
    uint32_t set_size = constants::MAX_FRAMES_IN_FLIGHT;
    uint32_t texture_binding_id = 3;
    // const uint32_t textures_count = textures.size();
    const uint32_t textures_count = MAX_TEXTURES_COUNT;

    // buffers
    std::vector<VBuffer> camera_buffers;
    uint32_t camera_size = sizeof(ogun::GPUCamera);
    VkDescriptorType camera_descriptor_type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    uint32_t camera_binding_id = 0;
    camera_buffers.resize(set_size);
    create_uniform_buffer(camera_buffers, camera_size, mproperties, device);
    shader_buffers.push_back(camera_buffers);

    std::vector<VBuffer> light_buffers;
    uint32_t light_size = sizeof(ogun::GPULight) * MAX_LIGHTS_COUNT;
    VkDescriptorType light_descriptor_type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    uint32_t light_binding_id = 1;
    light_buffers.resize(set_size);
    create_storage_buffer(light_buffers, light_size, mproperties, device);
    shader_buffers.push_back(light_buffers);

    std::vector<VBuffer> scene_buffers;
    uint32_t scene_size = sizeof(ogun::GPUScene);
    VkDescriptorType scene_descriptor_type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
    uint32_t scene_binding_id = 2;
    scene_buffers.resize(set_size);
    create_uniform_buffer(scene_buffers, scene_size, mproperties, device);
    shader_buffers.push_back(scene_buffers);
    
    // pools
    VkDescriptorPoolSize camera_pool;
    camera_pool.type = camera_descriptor_type;
    camera_pool.descriptorCount = static_cast<uint32_t>(set_size);

    VkDescriptorPoolSize light_pool;
    light_pool.type = light_descriptor_type;
    light_pool.descriptorCount = static_cast<uint32_t>(set_size);
    
    VkDescriptorPoolSize scene_pool;
    scene_pool.type = light_descriptor_type;
    scene_pool.descriptorCount = static_cast<uint32_t>(set_size);

    VkDescriptorPoolSize texture_pool;
    texture_pool.type = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
    texture_pool.descriptorCount = static_cast<uint32_t>(set_size);

    std::vector<VkDescriptorPoolSize> pools;
    pools.push_back(camera_pool);
    pools.push_back(light_pool);
    pools.push_back(scene_pool);
    pools.push_back(texture_pool);

    VkDescriptorPool descriptor_pool;
    VkDescriptorPoolCreateInfo pcreate_info{};
    pcreate_info.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
    pcreate_info.poolSizeCount = pools.size();
    pcreate_info.pPoolSizes = pools.data();
    pcreate_info.maxSets = static_cast<uint32_t>(set_size);
    checkvk(vkCreateDescriptorPool(device, &pcreate_info, nullptr, &descriptor_pool));

    // layouts
    VkDescriptorSetLayoutBinding camera_binding{};
    camera_binding.binding = camera_binding_id;
    camera_binding.descriptorCount = 1;
    camera_binding.descriptorType = camera_descriptor_type;
    camera_binding.pImmutableSamplers = nullptr;
    camera_binding.stageFlags = VK_SHADER_STAGE_VERTEX_BIT;
    
    VkDescriptorSetLayoutBinding light_binding{};
    light_binding.binding = light_binding_id;
    light_binding.descriptorCount = 1;
    light_binding.descriptorType = light_descriptor_type;
    light_binding.pImmutableSamplers = nullptr;
    light_binding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    VkDescriptorSetLayoutBinding scene_binding{};
    scene_binding.binding = scene_binding_id;
    scene_binding.descriptorCount = 1;
    scene_binding.descriptorType = scene_descriptor_type;
    scene_binding.pImmutableSamplers = nullptr;
    scene_binding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    VkDescriptorSetLayoutBinding texture_binding{};
    texture_binding.binding = texture_binding_id;
    texture_binding.descriptorCount = textures_count;
    texture_binding.descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
    texture_binding.pImmutableSamplers = nullptr;
    texture_binding.stageFlags = VK_SHADER_STAGE_FRAGMENT_BIT;

    std::vector<VkDescriptorSetLayoutBinding> uniform_bindings;
    uniform_bindings.push_back(camera_binding);
    uniform_bindings.push_back(light_binding);
    uniform_bindings.push_back(scene_binding);
    uniform_bindings.push_back(texture_binding);

    VkDescriptorSetLayout descriptor_layout;
    VkDescriptorSetLayoutCreateInfo layout_info{};
    layout_info.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
    layout_info.flags = 0;
    layout_info.pNext = nullptr;
    layout_info.bindingCount = uniform_bindings.size();
    layout_info.pBindings = uniform_bindings.data();
    checkvk(vkCreateDescriptorSetLayout(device,
        &layout_info,
        nullptr,
        &descriptor_layout));

    // sets
    std::vector<VkDescriptorSet> descriptor_set;
    std::vector<VkDescriptorSetLayout> layouts(set_size, descriptor_layout);
    VkDescriptorSetAllocateInfo dcreate_info{};
    dcreate_info.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
    dcreate_info.descriptorPool = descriptor_pool;
    dcreate_info.descriptorSetCount = static_cast<uint32_t>(set_size);
    dcreate_info.pSetLayouts = layouts.data();
    descriptor_set.resize(set_size);
    checkvk(vkAllocateDescriptorSets(device,
                                    &dcreate_info,
                                    descriptor_set.data()));
                                
    std::vector<VkWriteDescriptorSet> writes;
    for (size_t i = 0; i < set_size; i++) 
    {
        VkDescriptorBufferInfo camera_write_info{};
        camera_write_info.buffer = camera_buffers[i].buffer;
        camera_write_info.offset = 0;
        camera_write_info.range = camera_size;
    
        VkWriteDescriptorSet camera_write;
        camera_write.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        camera_write.pNext = NULL;
        camera_write.dstSet = descriptor_set[i];
        camera_write.dstBinding = camera_binding_id;
        camera_write.dstArrayElement = 0;
        camera_write.descriptorType = camera_descriptor_type;
        camera_write.descriptorCount = 1;
        camera_write.pBufferInfo = &camera_write_info;
        camera_write.pImageInfo = 0;

        VkDescriptorBufferInfo light_write_info{};
        light_write_info.buffer = light_buffers[i].buffer;
        light_write_info.offset = 0;
        light_write_info.range = light_size;
        
        VkWriteDescriptorSet light_write;
        light_write.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        light_write.pNext = NULL;
        light_write.dstSet = descriptor_set[i];
        light_write.dstBinding = light_binding_id;
        light_write.dstArrayElement = 0;
        light_write.descriptorType = light_descriptor_type;
        light_write.descriptorCount = 1;
        light_write.pBufferInfo = &light_write_info;
        light_write.pImageInfo = 0;
        
        VkDescriptorBufferInfo scene_write_info{};
        scene_write_info.buffer = scene_buffers[i].buffer;
        scene_write_info.offset = 0;
        scene_write_info.range = scene_size;
        
        VkWriteDescriptorSet scene_write;
        scene_write.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        scene_write.pNext = NULL;
        scene_write.dstSet = descriptor_set[i];
        scene_write.dstBinding = scene_binding_id;
        scene_write.dstArrayElement = 0;
        scene_write.descriptorType = scene_descriptor_type;
        scene_write.descriptorCount = 1;
        scene_write.pBufferInfo = &scene_write_info;
        scene_write.pImageInfo = 0;
        
        std::vector<VkDescriptorImageInfo> texture_write_info;
        texture_write_info.resize(textures_count);
        for (uint32_t i = 0; i < textures_count; i++)
        {
            texture_write_info[i].imageLayout = textures[i].imageLayout;
            texture_write_info[i].imageView = textures[i].imageView;
            texture_write_info[i].sampler = textures[i].sampler;
        }
        
        VkWriteDescriptorSet texture_write;
        texture_write.sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
        texture_write.pNext = NULL;
        texture_write.dstSet = descriptor_set[i];
        texture_write.dstBinding = texture_binding_id;
        texture_write.dstArrayElement = 0;
        texture_write.descriptorType = VK_DESCRIPTOR_TYPE_COMBINED_IMAGE_SAMPLER;
        texture_write.descriptorCount = texture_write_info.size();
        texture_write.pBufferInfo = 0;
        texture_write.pImageInfo = texture_write_info.data();

        writes = {};
        writes.push_back(camera_write);
        writes.push_back(light_write);
        writes.push_back(scene_write);
        writes.push_back(texture_write);
        vkUpdateDescriptorSets(device, writes.size(), writes.data(), 0, nullptr);
    }

    descriptor.sets = descriptor_set;
    descriptor.layout = descriptor_layout;
}

void create_framebuffer(std::vector<VkFramebuffer>& fbuffers, VkDevice device, VkRenderPass renderpass, VkExtent2D extent, std::vector<VkImageView> simages, std::vector<VkImageView> aimages)
{
    for (size_t i = 0; i < fbuffers.size(); i++)
    {
        std::vector<VkImageView> attachments = {};
        for (auto img : aimages)
            attachments.push_back(img);
        if (!simages.empty()) attachments.push_back(simages[i]);

        VkFramebufferCreateInfo create_info{};
        create_info.sType = VK_STRUCTURE_TYPE_FRAMEBUFFER_CREATE_INFO;
        create_info.renderPass = renderpass;
        create_info.attachmentCount = attachments.size();
        create_info.pAttachments = attachments.data();
        create_info.width = extent.width;
        create_info.height = extent.height;
        create_info.layers = 1;
        checkvk(vkCreateFramebuffer(device,
                                    &create_info,
                                    nullptr,
                                    &fbuffers[i]));
    }
}

void create_color_image(VImage& image, VkExtent2D extent, VkFormat format, VkSampleCountFlagBits samples, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device)
{
    VDeviceMemoryInfo image_device_memory_info = {
        VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
        mproperties
    };
    VImageInfo color_image_info = {
        1u,
        extent,
        format,
        VK_IMAGE_ASPECT_COLOR_BIT,
        VK_IMAGE_TILING_OPTIMAL,
        samples,
        VK_IMAGE_USAGE_TRANSIENT_ATTACHMENT_BIT | VK_IMAGE_USAGE_COLOR_ATTACHMENT_BIT
    };
    create_image(image, device, color_image_info, image_device_memory_info);
}

void create_depth_image(VImage& image, VkExtent2D extent, VkFormat format, VkSampleCountFlagBits samples, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device)
{
    VDeviceMemoryInfo image_device_memory_info = {
        VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
        mproperties
    };
    VImageInfo depth_image_info = {
        1u,
        extent,
        format,
        VK_IMAGE_ASPECT_DEPTH_BIT,
        VK_IMAGE_TILING_OPTIMAL,
        samples,
        VK_IMAGE_USAGE_DEPTH_STENCIL_ATTACHMENT_BIT
    };

    create_image(image, device, depth_image_info, image_device_memory_info);
}

void create_image(VImage& image, VkDevice device, VImageInfo info, VDeviceMemoryInfo minfo)
{
    VkImageCreateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_IMAGE_CREATE_INFO;
    create_info.imageType = VK_IMAGE_TYPE_2D;
    create_info.extent.width = info.extent.width;
    create_info.extent.height = info.extent.height;
    create_info.extent.depth = 1;
    create_info.mipLevels = info.mipLevels;
    create_info.arrayLayers = 1;
    create_info.format = info.format;
    create_info.tiling = info.tiling;
    create_info.initialLayout = VK_IMAGE_LAYOUT_UNDEFINED;
    create_info.usage = info.usage;
    create_info.samples = info.samples;
    create_info.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
    checkvk(vkCreateImage(device,
                                &create_info,
                                nullptr,
                                &image.img));

    // allocate and bind image memory
    VkMemoryRequirements memRequirements;
    vkGetImageMemoryRequirements(device, image.img, &memRequirements);
    VkMemoryAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    allocInfo.allocationSize = memRequirements.size;
    allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, minfo.flags, minfo.properties);
    checkvk(vkAllocateMemory(device,
                                &allocInfo,
                                nullptr,
                                &image.memory));
    vkBindImageMemory(device, image.img, image.memory, 0);

    // image view
    std::vector<VkImageView> views;
    std::vector<VkImage> imgs;
    views.push_back(image.view);
    imgs.push_back(image.img);
    create_imageview(views, device, imgs, info.format, info.aspect, info.mipLevels);
    image.view = views[0];
}

void create_imageview(std::vector<VkImageView>& views, VkDevice device, std::vector<VkImage> images, VkFormat format, VkImageAspectFlags aspectFlags, uint32_t mipLevels)
{
    for (int i = 0; i < images.size(); i++)
    {
        VkImageViewCreateInfo create_info = {};
        create_info.sType = VK_STRUCTURE_TYPE_IMAGE_VIEW_CREATE_INFO;
        create_info.image = images[i];
        create_info.viewType = VK_IMAGE_VIEW_TYPE_2D;
        create_info.format = format;
        create_info.components.r = VK_COMPONENT_SWIZZLE_IDENTITY;
        create_info.components.g = VK_COMPONENT_SWIZZLE_IDENTITY;
        create_info.components.b = VK_COMPONENT_SWIZZLE_IDENTITY;
        create_info.components.a = VK_COMPONENT_SWIZZLE_IDENTITY;
        create_info.subresourceRange.aspectMask = aspectFlags;
        create_info.subresourceRange.baseMipLevel = 0;
        create_info.subresourceRange.levelCount = mipLevels;
        create_info.subresourceRange.baseArrayLayer = 0;
        create_info.subresourceRange.layerCount = 1;
        checkvk(vkCreateImageView(device,
                                    &create_info,
                                    nullptr,
                                    &views[i]));
    }
}

void create_font(VFont& font)
{

}

void create_heightmap(VHeightMap& height_map)
{

}

void copy_image2buffer(VkImage& image, VkBuffer& buffer, VkExtent2D copy_extent, VSingleCommand& scmd)
{
    VkCommandBuffer cmd = begin_single_command(scmd.pool, scmd.device);
    VkBufferImageCopy region{};
    region.bufferOffset = 0;
    region.bufferRowLength = copy_extent.width;
    region.bufferImageHeight = copy_extent.height;
    region.imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    region.imageSubresource.mipLevel = 0;
    region.imageSubresource.baseArrayLayer = 0;
    region.imageSubresource.layerCount = 1;
    region.imageOffset = {0, 0, 0};
    region.imageExtent = {
        copy_extent.width,
        copy_extent.height,
        1
    };
    vkCmdCopyImageToBuffer(cmd, image, VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL, buffer, 1, &region);
    end_single_command(cmd, scmd.queue, scmd.pool, scmd.device);
}

void copy_buffer2image(VkBuffer buffer, VkImage image, VkExtent2D copy_extent, VSingleCommand scmd)
{
    VkCommandBuffer cmd = begin_single_command(scmd.pool, scmd.device);
    VkBufferImageCopy region{};
    region.bufferOffset = 0;
    region.bufferRowLength = 0;
    region.bufferImageHeight = 0;
    region.imageSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    region.imageSubresource.mipLevel = 0;
    region.imageSubresource.baseArrayLayer = 0;
    region.imageSubresource.layerCount = 1;
    region.imageOffset = {0, 0, 0};
    region.imageExtent = {
        copy_extent.width,
        copy_extent.height,
        1
    };
    vkCmdCopyBufferToImage(cmd, buffer, image, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, 1, &region);
    end_single_command(cmd, scmd.queue, scmd.pool, scmd.device);
}

void transition_image_layout(VkImage image, VkImageLayout old_layout, VkImageLayout new_layout, uint32_t mip_levels, VSingleCommand scmd)
{
    VkCommandBuffer cmd = begin_single_command(scmd.pool, scmd.device);
    VkImageMemoryBarrier barrier{};
    barrier.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
    barrier.oldLayout = old_layout;
    barrier.newLayout = new_layout;
    barrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.image = image;
    barrier.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    barrier.subresourceRange.baseMipLevel = 0;
    barrier.subresourceRange.levelCount = mip_levels;
    barrier.subresourceRange.baseArrayLayer = 0;
    barrier.subresourceRange.layerCount = 1;

    VkPipelineStageFlags sourceStage;
    VkPipelineStageFlags destinationStage;

    if (old_layout == VK_IMAGE_LAYOUT_UNDEFINED && new_layout == VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL) 
    {
        barrier.srcAccessMask = 0;
        barrier.dstAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        sourceStage = VK_PIPELINE_STAGE_TOP_OF_PIPE_BIT;
        destinationStage = VK_PIPELINE_STAGE_TRANSFER_BIT;
    } 
    else if (old_layout == VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL && new_layout == VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL) 
    {
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;
        sourceStage = VK_PIPELINE_STAGE_TRANSFER_BIT;
        destinationStage = VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT;
    } 
    else 
    {
        throw std::invalid_argument("unsupported layout transition!");
    }

    vkCmdPipelineBarrier(
        cmd,
        sourceStage, destinationStage,
        0,
        0, nullptr,
        0, nullptr,
        1, &barrier
    );

    end_single_command(cmd, scmd.queue, scmd.pool, scmd.device);
}

void generate_mipmap(VkImage image, VkFormatProperties format_properties, uint32_t mip_levels, VkExtent2D texture_extent, VSingleCommand scmd)
{
    // Check if image format supports linear imageFormat
    assert(format_properties.optimalTilingFeatures & VK_FORMAT_FEATURE_SAMPLED_IMAGE_FILTER_LINEAR_BIT);
    VkCommandBuffer cmd = begin_single_command(scmd.pool, scmd.device);

    VkImageMemoryBarrier barrier{};
    barrier.sType = VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER;
    barrier.image = image;
    barrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
    barrier.subresourceRange.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
    barrier.subresourceRange.baseArrayLayer = 0;
    barrier.subresourceRange.layerCount = 1;
    barrier.subresourceRange.levelCount = 1;

    int32_t mipWidth = texture_extent.width;
    int32_t mipHeight = texture_extent.height;

    for (uint32_t i = 1; i < mip_levels; i++) 
    {
        barrier.subresourceRange.baseMipLevel = i - 1;
        barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
        barrier.newLayout = VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL;
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        barrier.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;

        vkCmdPipelineBarrier(cmd,
            VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_TRANSFER_BIT, 0,
            0, nullptr,
            0, nullptr,
            1, &barrier);

        VkImageBlit blit{};
        blit.srcOffsets[0] = {0, 0, 0};
        blit.srcOffsets[1] = {mipWidth, mipHeight, 1};
        blit.srcSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        blit.srcSubresource.mipLevel = i - 1;
        blit.srcSubresource.baseArrayLayer = 0;
        blit.srcSubresource.layerCount = 1;
        blit.dstOffsets[0] = {0, 0, 0};
        blit.dstOffsets[1] = { mipWidth > 1 ? mipWidth / 2 : 1, mipHeight > 1 ? mipHeight / 2 : 1, 1 };
        blit.dstSubresource.aspectMask = VK_IMAGE_ASPECT_COLOR_BIT;
        blit.dstSubresource.mipLevel = i;
        blit.dstSubresource.baseArrayLayer = 0;
        blit.dstSubresource.layerCount = 1;

        vkCmdBlitImage(cmd,
            image, VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL,
            image, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL,
            1, &blit,
            VK_FILTER_LINEAR);

        barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_SRC_OPTIMAL;
        barrier.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
        barrier.srcAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
        barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

        vkCmdPipelineBarrier(cmd,
            VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT, 0,
            0, nullptr,
            0, nullptr,
            1, &barrier);

        if (mipWidth > 1) mipWidth /= 2;
        if (mipHeight > 1) mipHeight /= 2;
    }

    barrier.subresourceRange.baseMipLevel = mip_levels - 1;
    barrier.oldLayout = VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL;
    barrier.newLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
    barrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
    barrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;

    vkCmdPipelineBarrier(cmd,
        VK_PIPELINE_STAGE_TRANSFER_BIT, VK_PIPELINE_STAGE_FRAGMENT_SHADER_BIT, 0,
        0, nullptr,
        0, nullptr,
        1, &barrier);

    end_single_command(cmd, scmd.queue, scmd.pool, scmd.device);
}

VkCommandBuffer begin_single_command(VkCommandPool pool, VkDevice device)
{
    VkCommandBufferAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
    allocInfo.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
    allocInfo.commandPool = pool;
    allocInfo.commandBufferCount = 1;

    VkCommandBuffer cmd;
    vkAllocateCommandBuffers(device, &allocInfo, &cmd);

    VkCommandBufferBeginInfo beginInfo{};
    beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    beginInfo.flags = VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT;

    vkBeginCommandBuffer(cmd, &beginInfo);

    return cmd;
}

void end_single_command(VkCommandBuffer buffer, VkQueue queue, VkCommandPool pool, VkDevice device)
{
    vkEndCommandBuffer(buffer);

    VkSubmitInfo submitInfo{};
    submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    submitInfo.commandBufferCount = 1;
    submitInfo.pCommandBuffers = &buffer;

    VkResult result = vkQueueSubmit(queue, 1, &submitInfo, VK_NULL_HANDLE);
    vkQueueWaitIdle(queue);

    vkFreeCommandBuffers(device, pool, 1, &buffer);
}

void update_camera(float tick, uint32_t frame_index, ogun::GPUCamera camera)
{

}

void record_draw_commands(std::vector<VkCommandBuffer>& cmds, uint32_t image_index, std::vector<VkRenderPass> renderpass, std::vector<std::vector<VkFramebuffer>> framebuffer, VkExtent2D extent, VScene scene, std::vector<bool> passes_enabled)
{
    VkCommandBuffer cmd = cmds[image_index];
    VkCommandBufferBeginInfo zbeginInfo{};
    zbeginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    checkvk(vkBeginCommandBuffer(cmd, &zbeginInfo));
    {
        /* UI pass */
        bool ui_pass_enabled = false;
        if (ui_pass_enabled)
        {}

        /* blur pass */
        bool blur_pass_enabled = false;
        if (blur_pass_enabled)
        {}

        /* translucence pass */
        bool translucence_pass_enabled = false;
        if (translucence_pass_enabled)
        {}

        /* transparent,  pass */
        bool transparent_pass_enabled = false;
        if (transparent_pass_enabled)
        {}

        /* object pick pass */
        bool object_selectino_pass_enabled = false;
        if (object_selectino_pass_enabled)
        {   
            std::array<VkClearValue, 2> op_clearValues{};
            op_clearValues[0].color = {{0.0f, 0.0f, 0.0f, 1.0f}};
            op_clearValues[1].depthStencil = {1.0f, 1U};

            VkRenderPassBeginInfo op_renderPassInfo{};
            op_renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;
            op_renderPassInfo.renderPass = renderpass[1];
            op_renderPassInfo.framebuffer = framebuffer[1][image_index];
            op_renderPassInfo.renderArea.offset = {0, 0};
            op_renderPassInfo.renderArea.extent = extent;
            op_renderPassInfo.clearValueCount = static_cast<uint32_t>(op_clearValues.size());
            op_renderPassInfo.pClearValues = op_clearValues.data();

            vkCmdBeginRenderPass(cmd, &op_renderPassInfo, VK_SUBPASS_CONTENTS_INLINE);
            {}
            vkCmdEndRenderPass(cmd);
        }

        /* opaque render pass */
        std::array<VkClearValue, 2> clearValues{};
        clearValues[0].color = {{0.0f, 0.0f, 0.0f, 1.0f}};
        clearValues[1].depthStencil = {1.0f, 1U};

        VkRenderPassBeginInfo renderPassInfo{};
        renderPassInfo.sType = VK_STRUCTURE_TYPE_RENDER_PASS_BEGIN_INFO;
        renderPassInfo.renderPass = renderpass[0];
        renderPassInfo.framebuffer = framebuffer[0][image_index];
        renderPassInfo.renderArea.offset = {0, 0};
        renderPassInfo.renderArea.extent = extent;
        renderPassInfo.clearValueCount = static_cast<uint32_t>(clearValues.size());
        renderPassInfo.pClearValues = clearValues.data();

        uint32_t index_buffer_index = 0;
        vkCmdBeginRenderPass(cmd, &renderPassInfo, VK_SUBPASS_CONTENTS_INLINE);
        {
            if (passes_enabled[0])
            {
                // for (int i = 0; i < scene.materials.size(); i++)
                for (int i = 0; i < 2; i++)
                {
                    if (scene.materials[i].dynamic_states.viewport)
                    {
                        VkViewport viewport{};
                        viewport.x = 0.0f;
                        viewport.y = 0.0f;
                        viewport.width = (float) extent.width;
                        viewport.height = (float) extent.height;
                        viewport.minDepth = 0.0f;
                        viewport.maxDepth = 1.0f;
                        vkCmdSetViewport(cmd, 0, 1, &viewport);
                    }

                    if (scene.materials[i].dynamic_states.scissor)
                    {
                        VkRect2D scissor{};
                        scissor.offset = {0, 0};
                        scissor.extent = extent;
                        vkCmdSetScissor(cmd, 0, 1, &scissor);
                    }

                    // if VK_EXT_extended_dynamic_state supported
                    // if (scene.materials[i].dynamic_states.primitive_topology)
                    // {
                    //     vkCmdSetPrimitiveTopology(cmd, scene.materials[i].properties.topology);
                    // }

                    for (int i = 0; i < scene.push_constants.size(); i++)
                        vkCmdPushConstants(cmd, scene.materials[i].pipeline.pipeline, scene.push_constants[i].stage, scene.push_constants[i].offset, scene.push_constants[i].size, &scene.push_constants[i].pValues);

                    VkDeviceSize offsets[] = {0};
                    std::vector<VkBuffer> vertex_buffers;
                    uint32_t vertex_buffer_size = 0;
                    for (int k = 0; k < scene.vertex_buffers[i].size(); k++)
                    {
                        vertex_buffers.push_back(scene.vertex_buffers[i][k].buffer);
                        vertex_buffer_size += scene.vertex_buffers[i][k].size;
                    }
                    vkCmdBindPipeline(cmd,  scene.materials[i].pipeline.bpoint, scene.materials[i].pipeline.pipeline);
                    vkCmdBindVertexBuffers(cmd, 0, vertex_buffers.size(), vertex_buffers.data(), offsets);

                    std::vector<VkDescriptorSet> descriptors;
                    descriptors.push_back(scene.materials[i].descriptor.sets[image_index]);
                    vkCmdBindDescriptorSets(cmd, scene.materials[i].pipeline.bpoint, scene.materials[i].pipeline.layout, 0, static_cast<uint32_t>(descriptors.size()), descriptors.data(), 0, nullptr);

                    if (scene.materials[i].indexed)
                    {
                        vkCmdBindIndexBuffer(cmd, scene.index_buffers[i-index_buffer_index].buffer, 0, VK_INDEX_TYPE_UINT32);
                        vkCmdDrawIndexed(cmd, scene.index_buffers[i-index_buffer_index].size, 1, 0, 0, 0);
                    }
                    else
                    {
                        vkCmdDraw(cmd, vertex_buffer_size, 1, 0, 0);
                        index_buffer_index++;
                    }
                }
            }

            if (passes_enabled[1])
            {
                uint32_t i = 2;
                if (scene.materials[i].dynamic_states.viewport)
                {
                    VkViewport viewport{};
                    viewport.x = 0.0f;
                    viewport.y = 0.0f;
                    viewport.width = (float) extent.width;
                    viewport.height = (float) extent.height;
                    viewport.minDepth = 0.0f;
                    viewport.maxDepth = 1.0f;
                    vkCmdSetViewport(cmd, 0, 1, &viewport);
                }
                if (scene.materials[i].dynamic_states.scissor)
                {
                    VkRect2D scissor{};
                    scissor.offset = {0, 0};
                    scissor.extent = extent;
                    vkCmdSetScissor(cmd, 0, 1, &scissor);
                }
                VkDeviceSize offsets[] = {0};
                std::vector<VkBuffer> vertex_buffers;
                vertex_buffers.push_back(scene.vertex_buffers[i][image_index].buffer);
                vkCmdBindPipeline(cmd, VK_PIPELINE_BIND_POINT_GRAPHICS, scene.materials[i].pipeline.pipeline);
                vkCmdBindVertexBuffers(cmd, 0, vertex_buffers.size(), vertex_buffers.data(), offsets);
                vkCmdDraw(cmd, ogun::PARTICLE_COUNT, 1, 0, 0);
            }
        }
        vkCmdEndRenderPass(cmd);

        /* particle pass */
        // bool particle_pass_enabled = false;
        // if (particle_pass_enabled)
        // {   
        //     vkCmdBeginRenderPass(cmd, &renderPassInfo, VK_SUBPASS_CONTENTS_INLINE);
        //     {
        //         uint32_t i = 2;
        //         if (scene.materials[i].dynamic_states.viewport)
        //         {
        //             VkViewport viewport{};
        //             viewport.x = 0.0f;
        //             viewport.y = 0.0f;
        //             viewport.width = (float) extent.width;
        //             viewport.height = (float) extent.height;
        //             viewport.minDepth = 0.0f;
        //             viewport.maxDepth = 1.0f;
        //             vkCmdSetViewport(cmd, 0, 1, &viewport);
        //         }
        //         if (scene.materials[i].dynamic_states.scissor)
        //         {
        //             VkRect2D scissor{};
        //             scissor.offset = {0, 0};
        //             scissor.extent = extent;
        //             vkCmdSetScissor(cmd, 0, 1, &scissor);
        //         }
        //         VkDeviceSize offsets[] = {0};
        //         std::vector<VkBuffer> vertex_buffers;
        //         // uint32_t vertex_buffer_size = 0;
        //         // for (int k = 0; k < scene.vertex_buffers[i].size(); k++)
        //         // {
        //         //     vertex_buffers.push_back(scene.vertex_buffers[i][k].buffer);
        //         //     vertex_buffer_size += scene.vertex_buffers[i][k].size;
        //         // }
        //         vertex_buffers.push_back(scene.vertex_buffers[i][image_index].buffer);
        //         vkCmdBindPipeline(cmd, VK_PIPELINE_BIND_POINT_GRAPHICS, scene.materials[i].pipeline.pipeline);
        //         vkCmdBindVertexBuffers(cmd, 0, vertex_buffers.size(), vertex_buffers.data(), offsets);
        //         vkCmdDraw(cmd, ogun::PARTICLE_COUNT, 1, 0, 0);
        //     }
        //     vkCmdEndRenderPass(cmd);
        // }
    }
    checkvk(vkEndCommandBuffer(cmd));
}

void record_compute_commands(std::vector<VkCommandBuffer>& cmds, uint32_t image_index, std::vector<VkRenderPass> renderpass, std::vector<std::vector<VkFramebuffer>> framebuffer, VkExtent2D extent, VScene scene)
{
    VkCommandBuffer cmd = cmds[image_index];
    VkCommandBufferBeginInfo beginInfo{};
    beginInfo.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
    uint32_t compute_shader_local_size_x = 1;//256;
    // uint32_t compute_shader_local_size_x = 10;
    checkvk(vkBeginCommandBuffer(cmd, &beginInfo));
    {
        // for (int i = 0; i < scene.materials.size(); i++)
        // {
            uint32_t i = 3;
            vkCmdBindPipeline(cmd, scene.materials[i].pipeline.bpoint, scene.materials[i].pipeline.pipeline);
            std::vector<VkDescriptorSet> descriptors;
            descriptors.push_back(scene.materials[2].descriptor.sets[image_index]);
            vkCmdBindDescriptorSets(cmd, scene.materials[i].pipeline.bpoint, scene.materials[i].pipeline.layout, 0u, static_cast<uint32_t>(descriptors.size()), descriptors.data(), 0u, nullptr);
            vkCmdDispatch(cmd, ogun::PARTICLE_COUNT / compute_shader_local_size_x, 1u, 1u);
        // }

        // // headless compute
        // // Barrier to ensure that input buffer transfer is finished before compute shader reads from it
        // VkBufferMemoryBarrier bufferBarrier = vks::initializers::bufferMemoryBarrier();
        // bufferBarrier.buffer = deviceBuffer;
        // bufferBarrier.size = VK_WHOLE_SIZE;
        // bufferBarrier.srcAccessMask = VK_ACCESS_HOST_WRITE_BIT;
        // bufferBarrier.dstAccessMask = VK_ACCESS_SHADER_READ_BIT;
        // bufferBarrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
        // bufferBarrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;

        // vkCmdPipelineBarrier(
        //     commandBuffer,
        //     VK_PIPELINE_STAGE_HOST_BIT,
        //     VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
        //     VK_FLAGS_NONE,
        //     0, nullptr,
        //     1, &bufferBarrier,
        //     0, nullptr);

        // vkCmdBindPipeline(commandBuffer, VK_PIPELINE_BIND_POINT_COMPUTE, pipeline);
        // vkCmdBindDescriptorSets(commandBuffer, VK_PIPELINE_BIND_POINT_COMPUTE, pipelineLayout, 0, 1, &descriptorSet, 0, 0);

        // vkCmdDispatch(commandBuffer, BUFFER_ELEMENTS, 1, 1);

        // // Barrier to ensure that shader writes are finished before buffer is read back from GPU
        // bufferBarrier.srcAccessMask = VK_ACCESS_SHADER_WRITE_BIT;
        // bufferBarrier.dstAccessMask = VK_ACCESS_TRANSFER_READ_BIT;
        // bufferBarrier.buffer = deviceBuffer;
        // bufferBarrier.size = VK_WHOLE_SIZE;
        // bufferBarrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
        // bufferBarrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;

        // vkCmdPipelineBarrier(
        //     commandBuffer,
        //     VK_PIPELINE_STAGE_COMPUTE_SHADER_BIT,
        //     VK_PIPELINE_STAGE_TRANSFER_BIT,
        //     VK_FLAGS_NONE,
        //     0, nullptr,
        //     1, &bufferBarrier,
        //     0, nullptr);

        // // Read back to host visible buffer
        // VkBufferCopy copyRegion = {};
        // copyRegion.size = bufferSize;
        // vkCmdCopyBuffer(commandBuffer, deviceBuffer, hostBuffer, 1, &copyRegion);

        // // Barrier to ensure that buffer copy is finished before host reading from it
        // bufferBarrier.srcAccessMask = VK_ACCESS_TRANSFER_WRITE_BIT;
        // bufferBarrier.dstAccessMask = VK_ACCESS_HOST_READ_BIT;
        // bufferBarrier.buffer = hostBuffer;
        // bufferBarrier.size = VK_WHOLE_SIZE;
        // bufferBarrier.srcQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;
        // bufferBarrier.dstQueueFamilyIndex = VK_QUEUE_FAMILY_IGNORED;

        // vkCmdPipelineBarrier(
        //     commandBuffer,
        //     VK_PIPELINE_STAGE_TRANSFER_BIT,
        //     VK_PIPELINE_STAGE_HOST_BIT,
        //     VK_FLAGS_NONE,
        //     0, nullptr,
        //     1, &bufferBarrier,
        //     0, nullptr);
    }
    checkvk(vkEndCommandBuffer(cmd));
}

void load_resources(std::filesystem::path asset_library_path)
{
    std::filesystem::path font_library = asset_library_path / "fonts";
    std::filesystem::path heightmaps_library = asset_library_path / "heightmaps";
    std::filesystem::path images_library = asset_library_path / "images";
    std::filesystem::path textures_library = asset_library_path / "textures";
    std::filesystem::path models_library = asset_library_path / "models";

    // // get all resources in asset library directory and create corresponding objects
    // // textures
    // std::vector<VTexture> textures;
    // for (auto texture : textures)
    //     create_texture(texture);

    // // heightmaps
    // std::vector<VHeightMap> heightmaps;
    // for (auto hmap : heightmaps)
    //     create_heightmap(hmap);

    // // fonts
    // std::vector<VFont> fonts;
    // for (auto font : fonts)
    //     create_font(font);
}

void create_image_sampler(VkSampler& sampler, VkDevice device, float maxSamplerAnisotropy)
{
    VkSamplerCreateInfo create_info{};
    create_info.sType = VK_STRUCTURE_TYPE_SAMPLER_CREATE_INFO;
    create_info.magFilter = VK_FILTER_LINEAR;
    create_info.minFilter = VK_FILTER_LINEAR;
    create_info.addressModeU = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    create_info.addressModeV = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    create_info.addressModeW = VK_SAMPLER_ADDRESS_MODE_REPEAT;
    create_info.anisotropyEnable = VK_TRUE;
    create_info.maxAnisotropy = maxSamplerAnisotropy;
    create_info.borderColor = VK_BORDER_COLOR_INT_OPAQUE_BLACK;
    create_info.unnormalizedCoordinates = VK_FALSE;
    create_info.compareEnable = VK_FALSE;
    create_info.compareOp = VK_COMPARE_OP_ALWAYS;
    create_info.mipmapMode = VK_SAMPLER_MIPMAP_MODE_LINEAR;
    create_info.minLod = 0.0f;
    create_info.maxLod = VK_LOD_CLAMP_NONE;
    create_info.mipLodBias = 0.0f;
    checkvk(vkCreateSampler(device,
                                &create_info,
                                nullptr,
                                &sampler));
}

void load_textures(std::vector<VkDescriptorImageInfo>& textures, std::filesystem::path asset_library_path, VBuffer stage_buffer, VkPhysicalDevice pdevice, VkPhysicalDeviceMemoryProperties mproperties, VSingleCommand scmd, float maxSamplerAnisotropy)
{
    uint32_t tcount = 0;
    std::filesystem::path textures_library = asset_library_path / "textures";
    for (const auto & entry : std::filesystem::directory_iterator(textures_library))
    {
        VkDescriptorImageInfo texture;
        create_texture_image(texture, entry.path().string(), stage_buffer, pdevice, mproperties, scmd, maxSamplerAnisotropy);
        textures.push_back(texture);
        tcount++;
    }

    if (tcount < MAX_TEXTURES_COUNT)
    {
        for (int i = tcount; i < MAX_TEXTURES_COUNT; i++)
        {
            VkDescriptorImageInfo texture;
            create_texture_image(texture, "", stage_buffer, pdevice, mproperties, scmd, maxSamplerAnisotropy, true);
            textures.push_back(texture);
        }
    }
}


void create_texture_image(VkDescriptorImageInfo& texture, std::string texture_file, VBuffer& stage_buffer, VkPhysicalDevice pdevice, VkPhysicalDeviceMemoryProperties mproperties, VSingleCommand scmd, float maxSamplerAnisotropy, bool empty)
{
    VkSampler        texture_sampler;
    VkImageView      texture_imageView;
    VkImageLayout    texture_imageLayout = VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL;
    uint32_t mip_levels = 1u;
    VkExtent2D texture_extent = {};

    // sampler
    create_image_sampler(texture_sampler, scmd.device, maxSamplerAnisotropy);

    if (!empty)
    {
        // load texture file
        int texWidth, texHeight, texChannels;
        stbi_uc* pixels = stbi_load(texture_file.c_str(), &texWidth, &texHeight, &texChannels, STBI_rgb_alpha);
        VkDeviceSize imageSize = texWidth * texHeight * 4;
        mip_levels = static_cast<uint32_t>(std::floor(std::log2((std::max)(texWidth, texHeight)))) + 1;
        texture_extent = {static_cast<uint32_t>(texWidth), static_cast<uint32_t>(texHeight)};
        assert(pixels);
        void* data;
        vkMapMemory(scmd.device, stage_buffer.memory, 0, imageSize, 0, &data);
            memcpy(data, pixels, static_cast<size_t>(imageSize));
        vkUnmapMemory(scmd.device, stage_buffer.memory);
        stbi_image_free(pixels);
    }
    else
    {
        mip_levels = 1u;
        texture_extent = {1u, 1u};
    }

    // create image
    VkImageView texture_imageview;
    VImage texture_image;
    VkFormat texture_image_format = VK_FORMAT_R8G8B8A8_SRGB;
    VkImageAspectFlags texture_aspect = VK_IMAGE_ASPECT_COLOR_BIT;
    VDeviceMemoryInfo image_device_memory_info = {
        VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
        mproperties
    };
    VImageInfo color_image_info = {
        mip_levels,
        texture_extent,
        texture_image_format,
        texture_aspect,
        VK_IMAGE_TILING_OPTIMAL,
        VK_SAMPLE_COUNT_1_BIT,
        VK_IMAGE_USAGE_TRANSFER_SRC_BIT | VK_IMAGE_USAGE_TRANSFER_DST_BIT | VK_IMAGE_USAGE_SAMPLED_BIT
    };
    create_image(texture_image, scmd.device, color_image_info, image_device_memory_info);
    transition_image_layout(texture_image.img, VK_IMAGE_LAYOUT_UNDEFINED, VK_IMAGE_LAYOUT_TRANSFER_DST_OPTIMAL, mip_levels, scmd);
    copy_buffer2image(stage_buffer.buffer, texture_image.img, texture_extent, scmd);
    VkFormatProperties format_properties;
    vkGetPhysicalDeviceFormatProperties(pdevice, texture_image_format, &format_properties);
    generate_mipmap(texture_image.img, format_properties, mip_levels, texture_extent, scmd);
    std::vector<VkImageView> views;
    std::vector<VkImage> imgs;
    views.push_back(texture_imageview);
    imgs.push_back(texture_image.img);
    create_imageview(views, scmd.device, imgs, texture_image_format, texture_aspect, mip_levels);
    texture_imageView = views[0];
    
    // create texture
    texture.imageLayout = texture_imageLayout;
    texture.imageView = texture_imageView;
    texture.sampler = texture_sampler;
}

void checkvk(VkResult result)
{
    assert(result == VK_SUCCESS);
};

void query_pdevice_info(VkPhysicalDevice device,  VkSurfaceKHR surface, PDeviceInfo* deviceInfo)
{
    // query all available supported physical device extensions
    uint32_t extensionsCount;
    std::vector<VkExtensionProperties> availableExtension;
    vkEnumerateDeviceExtensionProperties(device, nullptr, &extensionsCount, nullptr);
    availableExtension.resize(extensionsCount);
    vkEnumerateDeviceExtensionProperties(device, nullptr, &extensionsCount, availableExtension.data());
    std::vector<std::string> extensions = {};
    for(auto extension : availableExtension)
        extensions.push_back(extension.extensionName);

    // queue family just describes a set of queues with identical properties
    vkGetPhysicalDeviceQueueFamilyProperties(device, &deviceInfo->queueFamilyPropertyCount, nullptr);
    deviceInfo->queueFamiliesProperties.resize(deviceInfo->queueFamilyPropertyCount);
    vkGetPhysicalDeviceQueueFamilyProperties(device, &deviceInfo->queueFamilyPropertyCount, deviceInfo->queueFamiliesProperties.data());

    // basic device properties for suitability query, e.g. name, 
    // type and supported Vulkan version
    vkGetPhysicalDeviceProperties(device, &(deviceInfo->properties));

    // support for optional features like texture compression, 
    // 64 bit floats and multi viewport rendering (useful for VR)
    vkGetPhysicalDeviceFeatures(device, &(deviceInfo->features));

    // Device memory properties
    vkGetPhysicalDeviceMemoryProperties(device, &deviceInfo->memoryProperties);

    // Get maximum usable multi sampling count available with given device
    deviceInfo->msaa_samples = maxUsableSampleCount(deviceInfo->properties);

    // query surface attributes and capabilities
    vkGetPhysicalDeviceSurfaceCapabilitiesKHR(device, surface, &deviceInfo->capabilities);

    // query the supported surface formats
    vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo->formatCount, nullptr);
    if (deviceInfo->formatCount != 0) 
    {
        deviceInfo->formats.resize(deviceInfo->formatCount);
        deviceInfo->formatProperties.resize(deviceInfo->formatCount);
        vkGetPhysicalDeviceSurfaceFormatsKHR(device, surface, &deviceInfo->formatCount, deviceInfo->formats.data());

        // query format properties
        for (int i=0; i<deviceInfo->formats.size(); i++)
        {
            vkGetPhysicalDeviceFormatProperties(device, deviceInfo->formats[i].format, &deviceInfo->formatProperties[i]);
        }
    }

    // query the supported presentation modes 
    vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo->presentModeCount, nullptr);
    if (deviceInfo->presentModeCount != 0) 
    {
        deviceInfo->present_modes.resize(deviceInfo->presentModeCount);
        vkGetPhysicalDeviceSurfacePresentModesKHR(device, surface, &deviceInfo->presentModeCount, deviceInfo->present_modes.data());
    }

    // query the supported depth format
    // m_defaultFormatFeatures(VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT)
    // , m_defaultTiling(VK_IMAGE_TILING_OPTIMAL)
    deviceInfo->formatFeatures = VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT;
    deviceInfo->tiling = VK_IMAGE_TILING_OPTIMAL;
    for (const auto &format  : DEPTH_FORMAT_CANDIDATES) 
    {
        VkFormatProperties props;
        vkGetPhysicalDeviceFormatProperties(device, format, &props);

        if (deviceInfo->tiling == VK_IMAGE_TILING_LINEAR && (props.linearTilingFeatures & deviceInfo->formatFeatures) == deviceInfo->formatFeatures)
        {
            deviceInfo->depth_format = format;
        } 
        else if (deviceInfo->tiling  == VK_IMAGE_TILING_OPTIMAL && (props.optimalTilingFeatures & deviceInfo->formatFeatures) == deviceInfo->formatFeatures)
        {
            deviceInfo->depth_format = format;
        }
    }
}

void query_pdevice_queue_info(VkPhysicalDevice device,  VkSurfaceKHR surface, std::vector<VkQueueFamilyProperties> queueFamiliesProperties, std::vector<VkDeviceQueueCreateInfo>& queueInfo)
{
    // Iterate through queue indices list to find which device specific
    // operations are supported by physical device on machine e.g. graphics,
    // presentation computation and memory transfer
    uint32_t i = 0;
    QueueFamilyIndices queueFamilyIndices;
    std::vector<VkDeviceQueueCreateInfo> queuecreate_infos;
    for (const auto& queueFamily : queueFamiliesProperties)
    {
        // Check for presentation support
        VkBool32 presentSupport;
        vkGetPhysicalDeviceSurfaceSupportKHR(device, i, surface, &presentSupport);
        
        if (queueFamily.queueFlags & VK_QUEUE_GRAPHICS_BIT) 
        {
            queueFamilyIndices.graphics = i;
            queueFamilyIndices.supported |= VK_QUEUE_GRAPHICS_BIT;
        }
        if (queueFamily.queueCount > 0 && presentSupport) 
        {
            i++;
            queueFamilyIndices.present = i;
            queueFamilyIndices.supported |= VK_QUEUE_GRAPHICS_BIT;
        }
        if (queueFamily.queueFlags & VK_QUEUE_COMPUTE_BIT) 
        { 
            i++;
            queueFamilyIndices.compute = i;
            queueFamilyIndices.supported |= VK_QUEUE_COMPUTE_BIT;
        }
        if (queueFamily.queueFlags & VK_QUEUE_TRANSFER_BIT) 
        {
            i++;
            queueFamilyIndices.transfer = i;
            queueFamilyIndices.supported |= VK_QUEUE_TRANSFER_BIT;
        }
        if (queueFamily.queueFlags & VK_QUEUE_SPARSE_BINDING_BIT) 
        {
            i++;
            queueFamilyIndices.sparse = i;
            queueFamilyIndices.supported |= VK_QUEUE_SPARSE_BINDING_BIT;
        }
        if(queueFamilyIndices.isComplete())
            break;
        i++;
    }

    // populate queue creation info vector // TEMP
    std::set<uint32_t> uniqueQueueFamilies = {
        queueFamilyIndices.graphics.value(),
        queueFamilyIndices.present.value(),
        queueFamilyIndices.compute.value(),
        queueFamilyIndices.transfer.value(),
        queueFamilyIndices.sparse.value(),
    };

    uint32_t queueCount = 1u;
    float queuePriority = 1.0f;
    for (uint32_t queueFamily : uniqueQueueFamilies)
    {
        VkDeviceQueueCreateInfo queuecreate_info{};
        queuecreate_info.sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO;
        queuecreate_info.queueFamilyIndex = queueFamily;
        queuecreate_info.queueCount = queueCount;
        queuecreate_info.pQueuePriorities = &queuePriority;
        queuecreate_infos.push_back(queuecreate_info);
    }
    queueInfo = queuecreate_infos;
}

uint32_t rate_pdevice(PDeviceInfo info, std::vector<VkDeviceQueueCreateInfo> queueInfo)
{
    uint32_t rating = 1;
    if (info.properties.deviceType == VK_PHYSICAL_DEVICE_TYPE_DISCRETE_GPU) rating++;
    return rating;
}

VkSampleCountFlagBits maxUsableSampleCount(VkPhysicalDeviceProperties deviceProperties)
{
    // https://stackoverflow.com/questions/5004858/why-is-stdmin-failing-when-windows-h-is-included
    // bypass #define NOMINMAX macro definition
    auto counts = (std::min)(deviceProperties.limits.framebufferColorSampleCounts,
                             deviceProperties.limits.framebufferDepthSampleCounts);
    for (const auto &sampleFlag : DEFAULT_STAGE_FLAG_BITS) 
    {
        if (counts & sampleFlag)
            return sampleFlag;
    }
    return VK_SAMPLE_COUNT_1_BIT;
}

VkSurfaceFormatKHR select_swapchain_surface_format(const std::vector<VkSurfaceFormatKHR>& availableFormats) 
{
    // https://stackoverflow.com/questions/12524623/what-are-the-practical-differences-when-working-with-colors-in-a-linear-vs-a-no
    for (const auto& availableFormat : availableFormats)
    {
        if (availableFormat.format == VK_FORMAT_B8G8R8A8_SRGB && availableFormat.colorSpace == VK_COLOR_SPACE_SRGB_NONLINEAR_KHR) 
        {
            return availableFormat;
        }
    }
    return availableFormats[0];
}

VkPresentModeKHR select_swapchain_present_modes(const std::vector<VkPresentModeKHR>& availablepresent_modes) 
{
    for (const auto& availablePresentMode : availablepresent_modes)
    {
        if (availablePresentMode == VK_PRESENT_MODE_MAILBOX_KHR)
        {
            return availablePresentMode;
        }
    }
    return VK_PRESENT_MODE_FIFO_KHR;
}

VkExtent2D select_swapchain_extent(const VkSurfaceCapabilitiesKHR& capabilities, VkExtent2D extent)
{
    if(capabilities.currentExtent.width != (std::numeric_limits<uint32_t>::max)())
    {
        return capabilities.currentExtent;
    } 
    else
    {
        VkExtent2D actualExtent = {
            static_cast<uint32_t>(extent.width),
            static_cast<uint32_t>(extent.height)
        };

        actualExtent.width = std::clamp(actualExtent.width, capabilities.minImageExtent.width, capabilities.maxImageExtent.width);
        actualExtent.height = std::clamp(actualExtent.height, capabilities.minImageExtent.height, capabilities.maxImageExtent.height);
        return actualExtent;
    }
}

VkFormat find_depth_format(VkPhysicalDevice pdevice)
{
    return find_support_format(pdevice,
        {VK_FORMAT_D32_SFLOAT, VK_FORMAT_D32_SFLOAT_S8_UINT, VK_FORMAT_D24_UNORM_S8_UINT},
        VK_IMAGE_TILING_OPTIMAL,
        VK_FORMAT_FEATURE_DEPTH_STENCIL_ATTACHMENT_BIT
    );
}

VkFormat find_support_format(VkPhysicalDevice pdevice, const std::vector<VkFormat>& candidates, VkImageTiling tiling, VkFormatFeatureFlags features)
{
    for (VkFormat format : candidates)
    {
        VkFormatProperties props;
        vkGetPhysicalDeviceFormatProperties(pdevice, format, &props);
        if (tiling == VK_IMAGE_TILING_LINEAR && (props.linearTilingFeatures & features) == features)
        {
            return format;
        } 
        else if (tiling == VK_IMAGE_TILING_OPTIMAL && (props.optimalTilingFeatures & features) == features)
        {
            return format;
        }
    }
    throw std::runtime_error("failed to find supported format!");
}


uint32_t findMemoryType(uint32_t typeFilter, VkMemoryPropertyFlags properties, VkPhysicalDeviceMemoryProperties memProperties)
{
    for (uint32_t i = 0; i < memProperties.memoryTypeCount; i++) 
    {
        if ((typeFilter & (1 << i)) && (memProperties.memoryTypes[i].propertyFlags & properties) == properties)
        {
            return i;
        }
    }
    throw std::runtime_error("failed to find suitable memory type!");
}

void load_shader_files(std::vector<VShaderModule>& shaders, std::filesystem::path asset_library_path, std::string package, std::string module, VkDevice device)
{
    std::filesystem::path shaders_path = asset_library_path / "shaders" / package;
    std::vector<std::string> extensions = {"comp", "frag", "vert", "geom", "tese", "tesc"};
    for (auto ext : extensions)
    {
        std::filesystem::path spath = shaders_path / (module + "." + ext  + ".spv");
        if ( std::filesystem::is_regular_file(spath))
        {
            VShaderModule shader;
            create_shader_module(shader.module, device, spath.string());
            
            if (ext == "comp")
                shader.stage = VK_SHADER_STAGE_COMPUTE_BIT;
            else if (ext == "geom")
                shader.stage = VK_SHADER_STAGE_GEOMETRY_BIT;
            else if (ext == "tese")
                shader.stage = VK_SHADER_STAGE_TESSELLATION_EVALUATION_BIT;
            else if (ext == "tesc")
                shader.stage = VK_SHADER_STAGE_TESSELLATION_CONTROL_BIT;
            else if (ext == "frag")
                shader.stage = VK_SHADER_STAGE_FRAGMENT_BIT;
            else if (ext == "vert")
                shader.stage = VK_SHADER_STAGE_VERTEX_BIT;
            else {}

            shader.entry_name = "main";
            shaders.push_back(shader);
        }
    }
}

std::vector<char> readFile(const std::string& filename)
{
    std::ifstream file(filename, std::ios::ate | std::ios::binary);
    if (!file.is_open())
    {
        throw std::runtime_error("failed to open file!");
    }

    // The advantage of starting to read at the end of the file is that we
    // can use the read position to determine the size of the file and allocate
    // a buffer
    size_t fileSize = (size_t) file.tellg();
    std::vector<char> buffer(fileSize);

    // seek back to the beginning of the file and read all of the bytes at once
    file.seekg(0);
    file.read(buffer.data(), fileSize);

    // close the file and return the bytes
    file.close();
    return buffer;
}

void copy_buffer(VkBuffer srcBuffer, VkBuffer dstBuffer, VkDeviceSize size, VkDeviceSize srcOffset, VkDeviceSize dstOffset, VSingleCommand& scmd)
{
    VkCommandBuffer cmd = begin_single_command(scmd.pool, scmd.device);
    VkBufferCopy copyRegion{};
    copyRegion.srcOffset = srcOffset;
    copyRegion.dstOffset = dstOffset;
    copyRegion.size = size;
    vkCmdCopyBuffer(cmd, srcBuffer, dstBuffer, 1, &copyRegion);
    end_single_command(cmd, scmd.queue, scmd.pool, scmd.device);
}

void create_stage_buffer(VBuffer& buffer, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device)
{
    VBufferInfo binfo = {
        VK_BUFFER_USAGE_TRANSFER_SRC_BIT,
        size,
        0
    };
    VDeviceMemoryInfo minfo = {
        VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT,
        mproperties
    };
    create_buffer(buffer, device, binfo, minfo);
}

void create_vertex_buffer(VBuffer& buffer, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device)
{
    VBufferInfo binfo = {
        VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT,
        size,
        0
    };
    VDeviceMemoryInfo minfo = {
        VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
        mproperties
    };
    create_buffer(buffer, device, binfo, minfo);
}

void create_index_buffer(VBuffer& buffer, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device)
{
    VBufferInfo binfo = {
        VK_BUFFER_USAGE_TRANSFER_DST_BIT | VK_BUFFER_USAGE_INDEX_BUFFER_BIT,
        size,
        0
    };
    VDeviceMemoryInfo minfo = {
        VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
        mproperties
    };
    create_buffer(buffer, device, binfo, minfo);
}

void create_storage_buffer(std::vector<VBuffer>& buffers, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device)
{
    VBufferInfo binfo = {
        VK_BUFFER_USAGE_STORAGE_BUFFER_BIT | VK_BUFFER_USAGE_VERTEX_BUFFER_BIT | VK_BUFFER_USAGE_TRANSFER_DST_BIT,
        size,
        0
    };
    VDeviceMemoryInfo minfo = {
        VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT,
        mproperties
    };

    for (int i = 0; i < buffers.size(); i++)
    {
        create_buffer(buffers[i], device, binfo, minfo);
    }
}

void create_uniform_buffer(std::vector<VBuffer>& buffers, VkDeviceSize size, VkPhysicalDeviceMemoryProperties mproperties, VkDevice device)
{
    VBufferInfo binfo = {
        VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT,
        size,
        0
    };
    VDeviceMemoryInfo minfo = {
        VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT,
        mproperties
    };

    for (int i = 0; i < buffers.size(); i++)
    {
        create_buffer(buffers[i], device, binfo, minfo);
        vkMapMemory(device, buffers[i].memory, 0, binfo.size, binfo.offset, &buffers[i].data);
    }
}

void create_buffer(VBuffer& buffer, VkDevice device, VBufferInfo info, VDeviceMemoryInfo minfo)
{
    VkBufferCreateInfo bufferInfo{};
    bufferInfo.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
    bufferInfo.size = info.size;
    bufferInfo.usage = info.usage;
    bufferInfo.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
    checkvk(vkCreateBuffer(device, &bufferInfo, nullptr, &buffer.buffer));

    VkMemoryRequirements memRequirements;
    vkGetBufferMemoryRequirements(device, buffer.buffer, &memRequirements);

    VkMemoryAllocateInfo allocInfo{};
    allocInfo.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
    allocInfo.allocationSize = memRequirements.size;
    allocInfo.memoryTypeIndex = findMemoryType(memRequirements.memoryTypeBits, minfo.flags, minfo.properties);
    checkvk(vkAllocateMemory(device, &allocInfo, nullptr, &buffer.memory));
    vkBindBufferMemory(device, buffer.buffer, buffer.memory, 0);
}

VKAPI_ATTR VkBool32 VKAPI_CALL debugCallback(VkDebugUtilsMessageSeverityFlagBitsEXT messageSeverity, VkDebugUtilsMessageTypeFlagsEXT messageType, const VkDebugUtilsMessengerCallbackDataEXT* pCallbackData, void* pUserData)
{
    std::cerr << "err validation layer: " << pCallbackData->pMessage << std::endl;
    return VK_FALSE;
}

void create_debugger(VkInstance instance, VkDebugUtilsMessengerEXT& debugMessenger)
{
    VkDebugUtilsMessengerCreateInfoEXT create_info = {};
    create_info.sType = VK_STRUCTURE_TYPE_DEBUG_UTILS_MESSENGER_CREATE_INFO_EXT;
    create_info.messageSeverity = VK_DEBUG_UTILS_MESSAGE_SEVERITY_VERBOSE_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_SEVERITY_WARNING_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_SEVERITY_ERROR_BIT_EXT;
    create_info.messageType = VK_DEBUG_UTILS_MESSAGE_TYPE_GENERAL_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_TYPE_VALIDATION_BIT_EXT | VK_DEBUG_UTILS_MESSAGE_TYPE_PERFORMANCE_BIT_EXT;
    create_info.pfnUserCallback = debugCallback;
    checkvk(CreateDebugUtilsMessengerEXT(instance, &create_info, nullptr, &debugMessenger));
}

VkResult CreateDebugUtilsMessengerEXT(VkInstance instance, const VkDebugUtilsMessengerCreateInfoEXT* pCreateInfo, const VkAllocationCallbacks* pAllocator, VkDebugUtilsMessengerEXT* pDebugMessenger)
{
    auto func = (PFN_vkCreateDebugUtilsMessengerEXT) vkGetInstanceProcAddr(instance, "vkCreateDebugUtilsMessengerEXT");
    if (func != nullptr) {
        return func(instance, pCreateInfo, pAllocator, pDebugMessenger);
    } else {
        return VK_ERROR_EXTENSION_NOT_PRESENT;
    }
}

void rebuild_swapchain(VkExtent2D extent)
{
    // SwapChainSupportDetails details = querySwapchainSupport(m_pdevice, m_surface);
    // VkExtent2D extent{m_width, m_height};
    // VSwapchain swapchain;
    // swapchain.device(m_device)
    //          .depth(m_deviceinfo.depthFormat)
    //          .surface(m_surface)
    //          .extent(extent)
    //          .presentModes(details.presentModes)
    //          .capabilities(details.capabilities)
    //          .formats(details.formats)
    //          .build(m_instance, m_pindices);
    // m_swapchain = swapchain;
}

void update_shaders(float tick, uint32_t image_index, std::vector<std::vector<VBuffer>> shader_buffers, ogun::VCamera primary_camera, ogun::GPUScene scene, glm::vec2 cursor)
{
    glm::mat4 projection_matrix = (primary_camera.projection_mode == 0) ? glm::perspective(primary_camera.zoom_angle, primary_camera.aspect, primary_camera.znear, primary_camera.zfar) : glm::ortho(0.0f, 1.0f, 1.0f, 0.0f, 0.1f, 200.0f);
    glm::mat4 view_matrix = glm::lookAt(primary_camera.position, primary_camera.front, primary_camera.up);
    glm::vec4 cursor_ray = glm::vec4{cursor.x, cursor.y, -1.0f, 1.0f};
    glm::mat4 projection_matrix_inverse = glm::inverse(projection_matrix);
    glm::mat4 view_matrix_inverse = glm::inverse(view_matrix);
    glm::vec4 cursor_ray_view = projection_matrix_inverse * cursor_ray;
    glm::vec4 cursor_ray_world = view_matrix_inverse * cursor_ray_view;
    // cursor_ray_view.z = -1.0f;
    // cursor_ray_view.w = 0.0f;
    // glm::vec4 cursor_ray_world = glm::normalize(view_matrix_inverse * cursor_ray_view);
    // std::cout << " cursor_ray_world coordinates x : y : z : w " << cursor_ray_world.x << " : " << cursor_ray_world.y <<  " : " << cursor_ray_world.z << " : " << cursor_ray_world.w << std::endl;

    // primary scene camera
    ogun::GPUCamera gcamera;
    gcamera.model = primary_camera.model;
    gcamera.view = view_matrix;
    gcamera.proj = projection_matrix;
    // gcamera.model = glm::rotate(primary_camera.model, rotation, glm::vec3(1.0f, 0.0f, 0.0f)normalized cursor position);
    // gcamera.model = glm::rotate(primary_camera.model, -primary_camera.zoom_angle, glm::vec3(0.0f, 0.0f, 1.0f));
    // if (primary_camera.projection_mode == 0)
    //     gcamera.proj = glm::perspective(primary_camera.zoom_angle, primary_camera.aspect, primary_camera.znear, primary_camera.zfar);
    //     // gcamera.proj = glm::perspective(primary_camera.zoom_angle, primary_camera.aspect, primary_camera.znear, primary_camera.zfar);
    // else 
    //     gcamera.proj = glm::ortho(0.0f, 1.0f, 1.0f, 0.0f, 0.1f, 200.0f);
    //     // glm::radians(45.0f)
    //     // glm::ortho(-(800.0f / 2.0f), 800.0f / 2.0f, 600.0f / 2.0f, -(600.0f / 2.0f), -10.0f, 50.0f);
    //     // gcamera.proj = glm::ortho(0.0f, 800.0f, 600.0f, 0.0f,-1000.0f, 1000.0f);
    gcamera.proj[1][1] *= -1;
    memcpy(shader_buffers[0][image_index].data, &gcamera, sizeof(gcamera));

    // scene data
    // ogun::GPUScene gscene;
    // gscene.view = glm::vec4{primary_camera.position.x, primary_camera.position.y, primary_camera.position.z, 1.0f};
    // gscene.parameters;
    memcpy(shader_buffers[1][image_index].data, &scene, sizeof(scene));

    // particles ubo
    // auto start = std::chrono::high_resolution_clock::now();
    // auto elapsed = std::chrono::high_resolution_clock::now() - start;
    // float microseconds = std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count();
    // uint64_t us = std::chrono::duration_cast<std::chrono::microseconds>(
    //         std::chrono::high_resolution_clock::now().time_since_epoch())
    //         .count();
    ogun::GPUParticlesParameters params;
    // params.deltaTime = tick * 1.0f;
    params.deltaTime = 3.0f;
    memcpy(shader_buffers[2][image_index].data, &params, sizeof(params));
}


void load_heightmap(uint32_t width, uint32_t height)
{
    // uint8_t resolution = 5u;
    // glm::vec4 color{1.0f, 0.0f, 0.0f, 1.0f};
    // int8_t direction = -1;
    // for (uint32_t i = 0; i < resolution-1; i++)
    // {
    //     for (uint32_t j = 0; j < resolution-1; j++)
    //     {
    //         TVertex vquad0;
    //         vquad0.position.x = (direction*(width / 2.0f)) + width*i/(float)resolution;
    //         vquad0.position.z = 0.0f;
    //         vquad0.position.y = (direction*(height / 2.0f)) + height*j/(float)resolution;
    //         vquad0.color = color;
    //         vquad0.texture.x = i / float(resolution);
    //         vquad0.texture.y = j / float(resolution);

    //         TVertex vquad1;
    //         vquad1.position.x = (direction*(width / 2.0f)) + width*(i+1)/(float)resolution;
    //         vquad1.position.z = 0.0f;
    //         vquad1.position.y = (direction*(height / 2.0f)) + height*j/(float)resolution;
    //         vquad1.color = color;
    //         vquad1.texture.x = (i+1) / float(resolution);
    //         vquad1.texture.y = j / float(resolution);
            
    //         TVertex vquad2;
    //         vquad2.position.x = (direction*(width / 2.0f)) + width*i/(float)resolution;
    //         vquad2.position.z = 0.0f;
    //         vquad2.position.y = (direction*(height / 2.0f)) + height*(j+1)/(float)resolution;
    //         vquad2.color = color;
    //         vquad2.texture.x = i / float(resolution);
    //         vquad2.texture.y = (j+1) / float(resolution);
            
    //         TVertex vquad3;
    //         vquad3.position.x = (direction*(width / 2.0f) ) + width*(i+1)/(float)resolution;
    //         vquad3.position.z = 0.0f;
    //         vquad3.position.y = (direction*(height / 2.0f)) + height*(j+1)/(float)resolution;
    //         vquad3.color = color;
    //         vquad3.texture.x = (i+1) / float(resolution);
    //         vquad3.texture.y = (j+1) / float(resolution);

    //         // quad vertices
    //         m_vertices.push_back(vquad0);
    //         m_vertices.push_back(vquad1);
    //         m_vertices.push_back(vquad2);
    //         m_vertices.push_back(vquad3);
    //     }
    // }
}

}; //  namespace vulkan