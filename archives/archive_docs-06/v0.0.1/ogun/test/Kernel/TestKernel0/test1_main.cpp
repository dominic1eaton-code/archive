/**
 * @header
 * @copyright
 * @brief
 * @note 
 */
#include "Hesabu/Window/HWindow.h"
#include "Ogun/Core/VInstance.h"
#include "Ogun/Core/VDevice.h"
#include "Ogun/Core/VSurface.h"
#include "Ogun/Core/VDescriptor.h"
#include "Ogun/Core/VPipeline.h"
// #include "Ogun/Core/VImage.h"
// #include "Ogun/Core/VCommand.h"

#include "Ogun/Core/VShaderManager.h"
#include "Ogun/Core/VSyncManager.h"

#include "Ogun/Buffer/VFrameBuffer.h"
#include "Ogun/Buffer/VSwapchain.h"


#include <iostream>
#include <unordered_map>
#include <string>
#include <queue>
#include <vector>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <chrono>

#define VK_USE_PLATFORM_WIN32_KHR


using namespace ogun;

/* shared data */
/** controls */
std::mutex mtx;
std::condition_variable cv;
bool data_ready = false;

/** messages */
int shared_data;

namespace kubatana
{
    class KSubscriber;

    // template<class U>
    class KMessage
    {
    public:
        KMessage() = default;

        KMessage(std::string header, std::string data) : m_header(header), m_data(data) {}

        virtual ~KMessage(void) = default;

        std::string header() const { return m_header; }

        std::string data() const { return m_data; }

    private:

        std::string m_header;

        std::string m_data;

    };

    class KArbiter
    {
    public:
        KArbiter() = default;
        
        virtual ~KArbiter(void) = default;

        void subscribe(const std::string& topic, KSubscriber* subscriber);

        void publish(const std::string& topic, KMessage* message);

        void processMessages();

    private:
    
        std::unordered_map<std::string, std::queue<KMessage*>> m_topics;

        std::unordered_map<std::string, std::vector<KSubscriber*>> m_subscribers;

        std::mutex m_mutex;

        std::condition_variable m_condition;

    };

    class KPublisher
    {
    public:
        KPublisher() = default;

        KPublisher(KArbiter& arbiter) : m_arbiter(&arbiter) {}

        virtual ~KPublisher(void) = default;

        void publish(const std::string& topic, KMessage* message)
        {
            m_arbiter->publish(topic, message);
        }

    private:

        KArbiter* m_arbiter;

    };
    
    class KSubscriber
    {
    public:
        KSubscriber() = default;

        KSubscriber(KArbiter& arbiter) : m_arbiter(&arbiter) {}

        virtual ~KSubscriber(void) = default;

        void subscribe(const std::string& topic)
        {
            m_arbiter->subscribe(topic, this);
        }

        virtual void receive(const KMessage* message, const std::string& topic);

    private:

        KArbiter* m_arbiter;

    };

    void KArbiter::publish(const std::string& topic, KMessage* message)
    {
        {
            std::lock_guard<std::mutex> lock(m_mutex);
            m_topics[topic].push(message);
        }
        m_condition.notify_all();
    }

    void KArbiter::subscribe(const std::string& topic, KSubscriber* subscriber)
    {
        std::lock_guard<std::mutex> lock(m_mutex);
        m_subscribers[topic].push_back(subscriber);
    }

    void KArbiter::processMessages()
    {
        std::unique_lock<std::mutex> lock(m_mutex);
        while(true)
        {
            m_condition.wait(lock, [this]
            {
                for (const auto &topic : m_topics)
                {
                    if (!topic.second.empty())
                    {
                        // message is empty
                        return true;
                    }
                }
                return false;
            });

            for (auto &topic : m_topics)
            {
                std::string topicName = topic.first;
                std::queue<KMessage*>& qMsgs = topic.second;
                while (!qMsgs.empty())
                {
                    KMessage* msg = qMsgs.front();
                    qMsgs.pop();
                    std::vector<KSubscriber*>& subscribers = m_subscribers[topicName];
                    for (auto &subscriber : subscribers)
                    {
                        subscriber->receive(msg, topicName);
                    }
                }
            }
        }
    }
}

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
        UBaseComponent() = default;
        virtual ~UBaseComponent(void) = default;
    
        uint32_t divisor() const { return m_divisor; }
    private:

        uint32_t m_divisor;
    };

    class UComponent : public UBaseComponent<UComponent>
    {
    public:
        UComponent() = default;
        virtual ~UComponent(void) = default;

    private:
        UInterface* m_interface;
    };
}

template<class U>
class Message
{
public:
    Message()
        : ready(false)
    {}

    virtual ~Message(void) = default;

    void arm()
    {
        std::lock_guard<std::mutex> lock(mtx);s
        ready = true;
        data_ready = true;
        cv.notify_all();
    }

    void disarm() { ready = false; }

    bool armed() const { return ready; }
    
    U data() const { return m_data; }

    void populate(U data) { m_data = data; }

private:

    bool ready;

    U m_data;
};

struct ogunWindowStateMessageData
{

    ogunWindowStateMessageData()
        : hwnd(nullptr)
        , name("")
        , width(600)
        , height(800)
    {}

    HWND hwnd;

    std::string name;

    uint32_t width;

    uint32_t height;
};

class ogunWindowStateMessage : public Message<ogunWindowStateMessageData>
{
public:

    ogunWindowStateMessage() = default;

    virtual ~ogunWindowStateMessage(void) = default;

private:

};

// struct ogunInputMouseMessage
// {
// };

// struct ogunInputKeyboardMessage
// {
// };

// struct ogunModelMessage
// {
// };

// class VExecutor
// {
// };

// class VInputManager
// {
// };

// class VWindowManager
// {
// };

/* execution threads */
void runInputManager()
{
    std::cout << "test input manager " << std::endl;

}

void runWindowManager()
{
    std::cout << "test vulkan window" << std::endl;

    hesabu::HWindow* window = new hesabu::HWindow();
    uint32_t status = 0;
    uint32_t nCmdShow = 1;
    if (!window->Create(L"Learn to Program Windows", WS_OVERLAPPEDWINDOW))
    {
        status = 1;
    }

    // send initial window state
    ogunWindowStateMessageData windowStateData;
    windowStateData.hwnd = window->hwnd();
    windowStateData.name = window->name();
    windowStateData.width = window->width();
    windowStateData.height = window->height();

    ogunWindowStateMessage* windowStateMsg = new ogunWindowStateMessage();
    windowStateMsg->populate(windowStateData);
    
    std::this_thread::sleep_for(std::chrono::seconds(5));
    {
        windowStateMsg->arm();
    }

    // perform window operations
    window->show(SW_SHOWNORMAL);
    window->message();

    // std::lock_guard<std::mutex> lock(mtx);
    // ogunWindowStateMessage windowMsg;
    // windowMsg.height = window->height();
    // windowMsg.width = window->width();
    // windowMsg.name = window->name();
    // windowMsg.hwnd = window->hwnd();
    // windowMsg.arm();

    // std::chrono::seconds duration(1);
    // window->show(SW_SHOWNORMAL);
    // std::this_thread::sleep_for( duration );
    // window->show(SW_HIDE);
    // std::this_thread::sleep_for( duration );
    // window->show(SW_SHOW);
    // std::this_thread::sleep_for( duration );
    // window->show(SW_MAXIMIZE);
    // std::this_thread::sleep_for( duration );
    // window->show(SW_MINIMIZE);
    // std::this_thread::sleep_for( duration );
    // window->show(SW_RESTORE);
}

void runExecutor()
{
    std::cout << "run vulkan model" << std::endl;

    // wait for receival of window state message
    // std::lock_guard<stdaronutex> lock(mtx);
    std::unique_lock<std::mutex> lock(mtx);
    cv.wait(lock, []{ return data_ready; });
    std::cout << "received window state message! proceeding with execution " << std::endl;

    /* core */
    VkApplicationInfo appInfo;
    appInfo.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
    appInfo.pApplicationName = "TestOgunEngine";
    appInfo.applicationVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.pEngineName = "TestOgunEngine";
    appInfo.engineVersion = VK_MAKE_VERSION(1, 0, 0);
    appInfo.apiVersion = VK_API_VERSION_1_0;

    VInstance instance;
    instance.info(appInfo)
            // .layers({"VK_LAYER_KHRONOS_validation"})
            .extensions({"VK_KHR_surface", "VK_KHR_win32_surface"})
            .build();

    // VSurface surface;
    // surface.hwnd(window->hwnd())
    //        .build(instance.inst());

    // VPhysicalDevice pdevice;
    // pdevice.select(instance.inst(), surface.surf());

    // VLogicalDevice ldevice;
    // ldevice.extensions({"VK_KHR_swapchain"})
    //        .device(pdevice.primary())
    //        .features(pdevice.info().features)
    //        .queueInfo(pdevice.queueInfo())
    //        .build(instance.inst());

    // // VCommandPool commandPool;
    // // VCommandBuffer commandBuffer;

    // VkExtent2D extent{window->width(), window->height()};
    // VSwapchain swapchain;
    // swapchain.device(ldevice.primary())
    //          .depth(pdevice.info().depthFormat)
    //          .surface(surface.surf())
    //          .extent(extent)
    //          .presentModes(pdevice.info().presentModes)
    //          .capabilities(pdevice.info().capabilities)
    //          .formats(pdevice.info().formats)
    //          .build(instance.inst());

    // VShaderManager* shaderManager = new VShaderManager("C:/dev/projects_v1.0.0/ogun/assets/shaders");
    // shaderManager->load(ldevice.primary());

    // VDescriptor descriptor;
    // descriptor.device(ldevice.primary())
    //           .build();

    // VGraphicsPipeline gpipeline;
    // gpipeline.device(ldevice.primary())
    //          .extent(swapchain.extent())
    //          .format(swapchain.format())
    //          .depth(pdevice.info().depthFormat)
    //          .layout(descriptor.layout())
    //          .shaders(shaderManager->shaders())
    //          .build();

    // std::vector<VFrameBuffer> frameBuffers;
    // std::vector<VImageView> imageViews;
    // VCommand command;
    // command.build();
    // VSyncManager* syncManager = new VSyncManager();
    // VDefaultPass* pass = new VDefaultPass();
    // VExecutor* executor = new VExecutor();
}

void testModel()
{
    std::cout << "test model" << std::endl;
    // kubatana::KArbiter arbiter;
    // std::thread arbiterThread(&kubatana::KArbiter::processMessages, &arbiter);
    // std::thread windowThread(runWindowManager, std::ref(arbiter));
    // std::thread inputThread(runInputManager, std::ref(arbiter));
    // std::thread executorThread(runExecutor, std::ref(arbiter));
    std::thread windowThread(runWindowManager);
    // std::thread inputThread(runInputManager);
    std::thread executorThread(runExecutor);

    windowThread.join();
    // inputThread.join();
    executorThread.join();
    // arbiterThread.join();
}


int main(int argc, char* argv[])
{
    testModel();
    return 0;
}
