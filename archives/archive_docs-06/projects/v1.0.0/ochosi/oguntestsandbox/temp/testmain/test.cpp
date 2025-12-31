


instanceLayers = (m_debugEnabled) ?  {"VK_LAYER_KHRONOS_validation"} : {""};
VInstance instance;
instance.info(appInfo)
        .layers(instanceLayers)
        .extensions({"VK_KHR_surface", "VK_KHR_win32_surface", "VK_EXT_debug_utils"})
        .build();

if (m_debugEnabled)
{
    VkDebugUtilsMessengerEXT debugMessenger;
    setupDebugMessenger(true, instance.inst(), debugMessenger);
}

VSurface surface;
surface.hwnd(config.window.hwnd)
       .build(instance.inst());

VPhysicalDevice pdevice;
pdevice.select(instance.inst(), surface.surf());

VLogicalDevice ldevice;
ldevice.extensions({"VK_KHR_swapchain", "VK_KHR_shader_draw_parameters"})
       .device(pdevice.primary())
       .features(pdevice.info().features)
       .queueInfo(pdevice.queueInfo())
       .build(instance.inst());

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
    
        
VkSampleCountFlagBits msaaSamples = VK_SAMPLE_COUNT_1_BIT;
VkPipelineBindPoint bindPoint = VK_PIPELINE_BIND_POINT_GRAPHICS;
VRenderPass renderpass;
renderpass.device(m_device)
          .format(swapchain.format())
          .depth(findDepthFormat(pdevice.primary()))
          .bindpoint(bindPoint)
          .samples(pdevice.info().msaaSamples)
          .build();



          
    // if (setcount == 0)
    // {
    //     VBuffer buffer;
    //     createbuffer();
    // }
    // else 
    // {
    //     std::vector<VBuffer> buffers;
    //     buffers.resize(setcount);
    //     for (size_t i = 0; i < setcount; i++)
    //     {
    //         createbuffer();
    //     }
    // }