/**
 * @header
 * @copyright
 * @brief
 * @note
 */

#include "vulkan_scene.h"
#include "Hesabu/Window/HWindow.h"

namespace usoro
{
    class UObject
    {
    public:
        UObject() = default;
        virtual ~UObject(void) = default;

        uint32_t id() const {return m_id; }

        std::string name() const { return m_name; }

    private:

        uint32_t m_id;

        std::string m_name;
    };

    class UImport
    {

    };

    class UExport
    {

    };

    class UInterface : public UObject
    {
    public:
        UInterface() = default;
        virtual ~UInterface(void) = default;

        /* send single message*/
        void send(std::string dest = "");
        
        /* receive single message*/
        void receive(std::string dest = "");

        /* publish one to many message */
        void publish();

        /* subscribe any to one message */
        void subscribe();
        
    private:
        UImport* m_import;

        UExport* m_export;
    };

    template <class DERIVED_TYPE> 
    class UBaseComponent : public UObject
    {
    public:
        UBaseComponent(std::string name, uint32_t id, uint32_t divisor) 
            : m_name(name)
            , m_id(id)
            , m_divisor(divisor)
            , m_active(false)
        {}

        virtual ~UBaseComponent(void) = default;
        
        std::string name() const { return m_name; }

        uint32_t id() const { return m_id; }
    
        uint32_t divisor() const { return m_divisor; }

        bool active() const { return m_active; }

        void activate() { m_active = true; }

        void deactivate() { m_active = false; }

    private:

        std::string m_name;

        uint32_t m_id;

        uint32_t m_divisor;

        bool m_active;
    };

    class UComponent : public UBaseComponent<UComponent>
    {
    public:
        UComponent()
            : UBaseComponent("", 0, 1)
        {}

        UComponent(std::string name, uint32_t id, uint32_t divisor) 
            : UBaseComponent(name, id, divisor)
        {}

        virtual ~UComponent(void) = default;

        virtual void initialize() = 0;

        virtual void configure() = 0;

        virtual void update() = 0;

        virtual void pause() = 0;

        virtual void reset() = 0;

        virtual void shutdown() = 0;

    private:

        UInterface* m_interface;

    };
}


namespace kubatana
{

const uint32_t MAX_BUFLEN = 1024;

class KBuffer
{
public:
    KBuffer() = default;

    virtual ~KBuffer(void) = default;

    void append(std::string data)
    {

    }

    void append(char data)
    {

    }

    void append(uint8_t data)
    {

    }

    void append(uint16_t data)
    {

    }

    void append(uint32_t data)
    {

    }

    void append(uint64_t data)
    {

    }
    
    void append(int8_t data)
    {

    }

    void append(int16_t data)
    {

    }

    void append(int32_t data)
    {

    }

    void append(int64_t data)
    {

    }

    void append(double data)
    {

    }

    void append(float data)
    {

    }

    void append(bool data)
    {

    }

    void prepend();

private:
    /* byte buffer */
    std::vector<std::byte> m_buffer;

};

struct KMessageHeader
{
    KMessageHeader()
    {}

    uint32_t id;
};

template<class U, class V>
class KMessage
{
public:
    KMessage()
        : ready(false)
    {
        m_dataBuffer = new KBuffer();
    }

    virtual ~KMessage(void) = default;

    void arm() 
    { 
        ready = true; 
        allocate();
    }

    void disarm() { ready = false; }

    bool armed() const { return ready; }
    
    U header() const { return m_header; }
    
    V data() const { return m_data; }

    void populate(U header, V data) 
    { 
        m_header = header;
        m_data = data; 
    }

    virtual void allocate() = 0;

    KBuffer* buffer() const { return m_dataBuffer; }

private:

    bool ready;

    U m_header;

    V m_data;
    
    KBuffer* m_dataBuffer;
};

class KClient
{
public:
   
    KClient() = default;

    virtual ~KClient(void) = default;

    void send();

    void recv();

private:

    const char* ipaddress;

};

class KServer
{
public:
   
    KServer() = default;

    virtual ~KServer(void) = default;

    void send();

    void recv();

private:

    const char* ipaddress;

};


}; // namespace kubatana



/* messages */
struct ogunWindowCreateMessageHeader : public kubatana::KMessageHeader
{
    ogunWindowCreateMessageHeader()
    {}
};

struct ogunWindowCreateMessageData
{
    ogunWindowCreateMessageData()
        : name("")
        , width(600)
        , height(800)
        , mode(hesabu::HWindowMode::NORMAL)
    {}

    std::string name;

    uint32_t width;

    uint32_t height;

    hesabu::HWindowMode mode;
};

class ogunWindowCreateMessage 
: public kubatana::KMessage<ogunWindowCreateMessageHeader, ogunWindowCreateMessageData>
{
public:

    ogunWindowCreateMessage() = default;

    virtual ~ogunWindowCreateMessage(void) = default;

    void allocate()
    {
        ogunWindowCreateMessageData dt = data();
        buffer()->append(dt.height);
        buffer()->append(dt.width);
        buffer()->append(dt.name);
    }
};


struct ogunWindowCreateResponseMessageData
{
    ogunWindowCreateResponseMessageData()
        : created(false)
    {}

    bool created;
};

class ogunWindowCreateResponseMessage 
: public kubatana::KMessage<ogunWindowCreateMessageHeader, ogunWindowCreateResponseMessageData>
{
public:

    ogunWindowCreateResponseMessage() = default;

    virtual ~ogunWindowCreateResponseMessage(void) = default;

    void allocate() {}
};



/* components */

/**
 * maintain state of scene
 */
class VSceneManager : public usoro::UComponent, kubatana::KServer
{
public:

    VSceneManager() = default;

    virtual ~VSceneManager(void) = default;

    void initialize() override;

    void configure() override;

    void update() override;

    void pause() override;

    void reset() override;

    void shutdown() override;

};

void VSceneManager::initialize()
{

}

void VSceneManager::configure()
{

}

void VSceneManager::update()
{

}

void VSceneManager::pause()
{

}

void VSceneManager::reset()
{

}

void VSceneManager::shutdown()
{

}


class VDataArbiter : public usoro::UComponent, kubatana::KServer
{
public:

    VDataArbiter() = default;

    virtual ~VDataArbiter(void) = default;

    void initialize() override;

    void configure() override;

    void update() override;

    void pause() override;

    void reset() override;

    void shutdown() override;

};

void VDataArbiter::initialize()
{

}

void VDataArbiter::configure()
{

}

void VDataArbiter::update()
{

}

void VDataArbiter::pause()
{

}

void VDataArbiter::reset()
{

}

void VDataArbiter::shutdown()
{

}


class VWindowManagerImport : public usoro::UImport
{

};

class VWindowManagerExport : public usoro::UExport
{

};


class VWindowManager : public usoro::UComponent, kubatana::KClient
{
public:

    VWindowManager() = default;

    virtual ~VWindowManager(void) = default;

    void initialize() override;

    void configure() override;

    void update() override;

    void pause() override;

    void reset() override;

    void shutdown() override;

    void create(ogunWindowCreateMessageData data);

};

void VWindowManager::initialize()
{

    // recv()
}

void VWindowManager::configure()
{

}

void VWindowManager::update()
{
    ogunWindowCreateMessageData data;
    data.name = "hesabu window";
    data.height = 800;
    data.width = 600;
    data.mode = hesabu::HWindowMode::NORMAL;
    create(data);
    deactivate();
}

void VWindowManager::pause()
{

}

void VWindowManager::reset()
{

}

void VWindowManager::shutdown()
{

}

void VWindowManager::create(ogunWindowCreateMessageData data)
{
    std::wstring widestr = std::wstring(data.name.begin(), data.name.end());
    const wchar_t* name = widestr.c_str();
    hesabu::HWindow* window = new hesabu::HWindow();
    uint32_t status = 0;
    uint32_t nCmdShow = 1;
    if (!window->Create(name, WS_OVERLAPPEDWINDOW))
    {
        status = 1;
    }
    window->show();
    window->message();

}

enum class ExecutorModelType
{
    VULKAN
};

struct ExecutorModelInfo
{

};

template<typename T>
class ExecutorModel
{
public:

    ExecutorModel() = default;

    virtual ~ExecutorModel(void) = default;

    virtual void init(T info) = 0;

    virtual void begin() = 0;

    virtual void draw(float tick) = 0;

    virtual void shutdown() = 0;

};

struct WindowInfo
{
public:
    WindowInfo()
    {}

    HWND hwnd;

    std::string name;

    uint32_t height;

    uint32_t width;
};

struct VulkanModelInfo : public ExecutorModelInfo
{
public:
    VulkanModelInfo()
    {}

    WindowInfo window;

    // std::unordered_map<std::string, std::string> m_paths; // <file name, absolute path>
    
    std::string shaderLibraryPath;
};

class VulkanModel : public ExecutorModel<VulkanModelInfo>
{
public:

    VulkanModel();

    virtual ~VulkanModel(void) = default;

    void init(VulkanModelInfo info);
    
    void begin();

    void draw(float tick);

    void shutdown();

private:

    std::vector<VkDescriptorSet> m_descriptorSets;

    uint32_t m_frameIndex;

    VkDevice m_device;

    VFences* m_fences;

    VSemaphores* m_semaphores;

    VSwapchain m_swapchain;

    TestShader0* m_shader;

    std::vector<VkQueue> m_queues;
    
    std::vector<VkCommandBuffer> m_commandBuffers;

    VkRenderPass m_renderpass;
    
    std::vector<VkFramebuffer> m_framebuffers;
    
    std::vector<VkPipeline> m_pipelines;
    
    std::vector<VkBuffer> m_vertexBuffers;
    
    VkBuffer m_indexBuffer;
    
    VkPipelineLayout m_layout;
    
    uint32_t m_indicesCount;

};

VulkanModel::VulkanModel()
    : m_frameIndex(0)
{
    m_fences = new VFences();
    m_semaphores = new VSemaphores();
    m_shader = new TestShader0();
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
    /* core objects */
    VkApplicationInfo appInfo;
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "TestOgunEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "TestOgunEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    VInstance instance;
    instance.info(appInfo)
            .layers({"VK_LAYER_KHRONOS_validation"}) // @todo figure out path issue
            .extensions({"VK_KHR_surface", "VK_KHR_win32_surface"})
            .build();

    VSurface surface;
    surface.hwnd(info.window.hwnd)
           .build(instance.inst());

    VPhysicalDevice pdevice;
    pdevice.select(instance.inst(), surface.surf());

    VLogicalDevice ldevice;
    ldevice.extensions({"VK_KHR_swapchain"})
           .device(pdevice.primary())
           .features(pdevice.info().features)
           .queueInfo(pdevice.queueInfo())
           .build(instance.inst());
    m_device = ldevice.primary();
    m_queues = ldevice.queues();

    VkExtent2D extent{info.window.width, info.window.height};
    VSwapchain swapchain;
    swapchain.device(m_device)
             .depth(pdevice.info().depthFormat)
             .surface(surface.surf())
             .extent(extent)
             .presentModes(pdevice.info().presentModes)
             .capabilities(pdevice.info().capabilities)
             .formats(pdevice.info().formats)
             .build(instance.inst(), pdevice.indices());
    m_swapchain = swapchain;

    VkPipelineBindPoint bindPoint = VK_PIPELINE_BIND_POINT_GRAPHICS;
    VRenderPass renderpass;
    renderpass.device(m_device)
              .format(swapchain.format())
              .depth(pdevice.info().depthFormat)
              .bindpoint(bindPoint)
              .build();
    m_renderpass = renderpass.pass();

    m_fences->create("inflight", ogun::constants::MAX_FRAMES_IN_FLIGHT, VK_FENCE_CREATE_SIGNALED_BIT, m_device);
    m_semaphores->create("imageAvailable", ogun::constants::MAX_FRAMES_IN_FLIGHT, m_device);
    m_semaphores->create("renderFinished", ogun::constants::MAX_FRAMES_IN_FLIGHT, m_device);
    VkCommandPool commandPool = createCommandPool(m_device, pdevice.indices().graphics);
    m_commandBuffers = createCommandBuffers(m_device, commandPool);

    /* resources */
    VkSampleCountFlagBits msaaSamples = VK_SAMPLE_COUNT_1_BIT;
    VkImage textureImage;
    VkImage colorImage;
    VkImage depthImage;
    VkDeviceMemory textureImageMemory;
    VkDeviceMemory colorImageMemory;
    VkDeviceMemory depthImageMemory;
    std::string testTextureImage = "D:/dev/projects_v1.0.0/ogun/assets/textures/grass-texture-background.jpg";
    uint32_t mipLevels;
    VkSampler textureSampler;
    VkImageView textureImageView;
    VkImageView colorImageView;
    VkImageView depthImageView;
    createTextureImage(pdevice.primary(), m_device, testTextureImage, ldevice.queues()[0], commandPool, pdevice.info().memoryProperties, textureImage, textureImageMemory, mipLevels);
    createTextureImageView(m_device, textureImage, mipLevels, textureImageView);
    createTextureSampler(pdevice.info().properties, m_device, textureSampler);
    createColorResources(m_device, m_swapchain.format(), pdevice.info().msaaSamples, colorImage, colorImageMemory, m_swapchain.extent(), pdevice.info().memoryProperties, 1u, colorImageView);
    createDepthResources(m_device, pdevice.primary(), pdevice.info().msaaSamples, depthImage, depthImageMemory, m_swapchain.extent(), pdevice.info().memoryProperties, 1u, depthImageView);
    createFramebuffers(m_device, m_swapchain.extent(), m_renderpass, colorImageView, depthImageView, m_swapchain.imageViews(), m_framebuffers);

    /* scene data */
    std::vector<VertexShaderData> vertices{};
    std::vector<uint16_t> indices{};
    std::vector<GPUMeshData> models{};
    load_scene(vertices, indices, models);
    m_indicesCount = indices.size();

    /* pipeline(s) */
    VkDescriptorSetLayout descriptorSetLayout;
    m_shader = new TestShader0();
    m_shader->load(vertices, indices, models, m_queues[0], commandPool, pdevice.info().memoryProperties,
                   m_device, descriptorSetLayout, textureSampler, m_swapchain.extent(), textureImageView, VK_IMAGE_LAYOUT_SHADER_READ_ONLY_OPTIMAL);
    m_indexBuffer = m_shader->indexBuffer();
    m_vertexBuffers = m_shader->vertexBuffers();

    VShaderManager* shaderManager = new VShaderManager(info.shaderLibraryPath);
    shaderManager->load(m_device);

    VGraphicsPipeline gpipeline;
    gpipeline.device(m_device)
             .pass(m_renderpass)
             .extent(swapchain.extent())
             .layout(descriptorSetLayout)
             .shaders(shaderManager->shaders())
             .build();
    m_pipelines.push_back(gpipeline.pipeline());
    m_layout = gpipeline.pipelineLayout();
    m_descriptorSets = m_shader->descriptorSets();
};

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
        m_swapchain.rebuild();
        return;
    } 
    else if (result != VK_SUCCESS && result != VK_SUBOPTIMAL_KHR) 
    {
        throw std::runtime_error("failed to acquire swap chain image!");
    }

    VkExtent2D extent = m_swapchain.extent();
    std::vector<void*> uniformBuffersMapped;
    m_shader->update(tick, m_frameIndex);

    vkResetFences(m_device, 1, &inFlightFences[m_frameIndex]);
    vkResetCommandBuffer(m_commandBuffers[m_frameIndex], 0);

    std::vector<VkDescriptorSet> descriptorSets;
    descriptorSets.push_back(m_descriptorSets[m_frameIndex]);
    recordCommandBuffer(m_commandBuffers[m_frameIndex], imageIndex, m_renderpass, extent, m_framebuffers[m_frameIndex], m_pipelines[0], 
                        m_vertexBuffers, m_indexBuffer, m_layout, descriptorSets, m_indicesCount);
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

    VkSubmitInfo submitInfo{};
    submitInfo.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
    submitInfo.pNext = NULL;
    submitInfo.waitSemaphoreCount = waitSemaphores.size();
    submitInfo.pWaitSemaphores = waitSemaphores.data();
    submitInfo.pWaitDstStageMask = waitStages;
    submitInfo.commandBufferCount = submitBuffers.size();
    submitInfo.pCommandBuffers = submitBuffers.data();
    submitInfo.signalSemaphoreCount = signalSemaphores.size();
    submitInfo.pSignalSemaphores = signalSemaphores.data();

    if (vkQueueSubmit(m_queues[0], 1, &submitInfo, inFlightFences[m_frameIndex]) != VK_SUCCESS) 
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

    bool framebufferResized = false;
    if (result == VK_ERROR_OUT_OF_DATE_KHR || result == VK_SUBOPTIMAL_KHR || framebufferResized) 
    {
        framebufferResized = false;
        m_swapchain.rebuild();
    }
    else if (result != VK_SUCCESS) 
    {
        throw std::runtime_error("failed to present swap chain image!");
    }

    m_frameIndex = (m_frameIndex + 1) % ogun::constants::MAX_FRAMES_IN_FLIGHT;
}

class VOgunExecutor : public usoro::UComponent, kubatana::KClient
{
public:

    VOgunExecutor()
        : m_bWindowCreated(false)
        , m_bVulkanInitialized(false)
        , m_modeType(ExecutorModelType::VULKAN)
    {
        if (m_modeType == ExecutorModelType::VULKAN)
        {
            m_model = new (VulkanModel);
        }
    }

    virtual ~VOgunExecutor(void) = default;

    void initialize() override;

    void configure() override;

    void update() override;

    void pause() override;

    void reset() override;

    void shutdown() override;

private:

    bool m_bWindowCreated;

    bool m_bVulkanInitialized;

    ExecutorModel<VulkanModelInfo>* m_model;

    ExecutorModelType m_modeType;

};

void VOgunExecutor::initialize()
{
 
}

void VOgunExecutor::configure()
{
    if (!m_bWindowCreated)
    {
        ogunWindowCreateMessageData data;
        ogunWindowCreateMessageHeader header;
        ogunWindowCreateMessage* windowCreateMsg = new ogunWindowCreateMessage();
        ogunWindowCreateResponseMessage* windowCreateResponseMsg = new ogunWindowCreateResponseMessage();

        // send initial window creation message to window manager
        header.id = 1000;
        data.name = "hesabu window";
        data.height = 800;
        data.width = 600;
        data.mode = hesabu::HWindowMode::NORMAL;
        windowCreateMsg->populate(header, data);
        windowCreateMsg->arm();
        // send(windowCreateMsg);
        
        // // wait for window manager create window response
        // while(recv(windowCreateResponseMsg))
        // {
            m_bWindowCreated = true;
        // }

        // temp receive message time delay simulate
        std::this_thread::sleep_for(std::chrono::seconds(3));

        if (!(m_bVulkanInitialized && m_bWindowCreated))
        {
            //     FindWindow(data.name);
            VulkanModelInfo info;
            info.window.hwnd = FindWindow(data.name.c_str(), 0);
            info.window.name = data.name;
            info.window.height = data.height;
            info.window.width = data.width;
            info.shaderLibraryPath = "D:/dev/projects_v1.0.0/ogun/assets/shaders";
            m_model->init(info);
        }
    }
}

void VOgunExecutor::update()
{
    static auto startTime = std::chrono::high_resolution_clock::now();
    auto currentTime = std::chrono::high_resolution_clock::now();
    float tick = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();
    m_model->draw(tick);
}

void VOgunExecutor::pause()
{

}

void VOgunExecutor::reset()
{

}

void VOgunExecutor::shutdown()
{
   m_model->shutdown();
}

void runWindowManager()
{
    std::cout << "running window manager" << std::endl;
    VWindowManager* windowManager = new VWindowManager();
    windowManager->activate();
    windowManager->initialize();
    windowManager->configure();
    windowManager->pause();
    while(windowManager->active()) { windowManager->update(); }
    windowManager->reset();
    windowManager->shutdown();
}

void runVulkanExecutor()
{
    std::cout << "running vulkan executor" << std::endl;
    VOgunExecutor* executor = new VOgunExecutor();
    executor->activate();
    executor->initialize();
    executor->configure();
    executor->pause();
    while(executor->active()) { executor->update(); }
    executor->reset();
    executor->shutdown();
}

void runDataArbiterServer()
{
    std::cout << "running data arbiter" << std::endl;
    VDataArbiter* arbiter = new VDataArbiter();
    arbiter->activate();
    arbiter->initialize();
    arbiter->configure();
    arbiter->pause();
    while(arbiter->active()) { arbiter->update(); }
    arbiter->reset();
    arbiter->shutdown();
}

void runSceneManager()
{
    std::cout << "running scene manager" << std::endl;
    VSceneManager* sceneManager = new VSceneManager();
    sceneManager->activate();
    sceneManager->initialize();
    sceneManager->configure();
    sceneManager->pause();
    while(sceneManager->active()) { sceneManager->update(); }
    sceneManager->reset();
    sceneManager->shutdown();
}

void testModel()
{
    std::cout << "run test kernel model" << std::endl;
    std::thread windowManagerThread(runWindowManager);
    std::thread vulkanExecutorThread(runVulkanExecutor);
    std::thread sceneManagerThread(runSceneManager);
    std::thread dataArbiterServerThread(runDataArbiterServer);

    glm::vec3 testvector(1, 3, 4);
    std::cout << "test vector " << testvector.x << " " << testvector.y << " " << testvector.z << std::endl;

    windowManagerThread.join();
    vulkanExecutorThread.join();
    sceneManagerThread.join();
    dataArbiterServerThread.join();
}

int main(int argc, char* argv[])
{
    testModel();
    return 0;
}

