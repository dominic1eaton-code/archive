/**
 * @file main.cpp
 * @header
 * @copyright
 * @brief
 * @note
 */

// #include "vulkan_scene.h"
// #include <filesystem>

#include "vulkan_exec.h"

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

    class UData
    {};

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

class VWindowManagerImport : public usoro::UImport
{

};

class VWindowManagerExport : public usoro::UExport
{

};


struct EngineStats {
    float frametime;
    int triangle_count;
    int drawcall_count;
    float mesh_draw_time;
};

class VWindowManager  : public usoro::UComponent //, kubatana::KClient
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

    hesabu::HWindow* window;

    EngineStats stats;

};

void VWindowManager::initialize()
{
    ogunWindowCreateMessageData data;
    data.name = "hesabu window";
    data.height = 800;
    data.width = 600;
    data.mode = hesabu::HWindowMode::NORMAL;
    create(data);
}

void VWindowManager::configure()
{

}

void VWindowManager::update()
{
    auto start = std::chrono::system_clock::now();
    // window->poll();
    // uint32_t inputstate = window->state();
    // std::cout << "input state: " << inputstate << std::endl;
    int e = 0;
    uint32_t event;
    window->pollEvent(event);
    std::cout << "event code: " << event << std::endl;

    auto end = std::chrono::system_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::microseconds>(end - start);

    stats.frametime = elapsed.count() / 1000.f;
    // deactivate();
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
    data.name = "OgunEngine";
    std::wstring widestr = std::wstring(data.name.begin(), data.name.end());
    window = new hesabu::HWindow();
    window->create(widestr.c_str());
    // window->init();
    window->show();
    // window->message();
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

// void testModel()
// {
//     std::cout << "run test kernel model" << std::endl;
//     std::thread windowManagerThread(runWindowManager);
//     windowManagerThread.join();
// }


class VOgunExecutor : public usoro::UComponent//, kubatana::KClient
{
public:

    VOgunExecutor()
        : m_bWindowCreated(false)
        , m_bVulkanInitialized(false)
        // , m_modeType(ExecutorModelType::VULKAN)
    {
        // if (m_modeType == ExecutorModelType::VULKAN)
        // {
        //     m_model = new (VulkanModel);
        // }
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

    // ExecutorModel<VulkanModelInfo>* m_model;

    // ExecutorModelType m_modeType;

};

void VOgunExecutor::initialize()
{
 
}



// Callback function that handles events.
//
void CALLBACK HandleWinEvent(HWINEVENTHOOK hook, DWORD event, HWND hwnd,
    LONG idObject, LONG idChild,
    DWORD dwEventThread, DWORD dwmsEventTime)
{
    // std::cout << "calling HandleWinEvent callback" << std::endl;
    // IAccessible* pAcc = NULL;
    // VARIANT varChild;
    // HRESULT hr = AccessibleObjectFromEvent(hwnd, idObject, idChild, &pAcc, &varChild);  
    // if ((hr == S_OK) && (pAcc != NULL))
    // {
    //     BSTR bstrName;
    //     pAcc->get_accName(varChild, &bstrName);
    //     if (event == EVENT_SYSTEM_MENUSTART)
    //     {
    //     printf("Begin: ");
    //     }
    //     else if (event == EVENT_SYSTEM_MENUEND)
    //     {
    //     printf("End:   ");
    //     }
    //     printf("%S\n", bstrName);
    //     SysFreeString(bstrName);
    //     pAcc->Release();
    // }
}

void VOgunExecutor::configure()
{
    if (!m_bWindowCreated)
    {
        // ogunWindowCreateMessageData data;
        // ogunWindowCreateMessageHeader header;
        // ogunWindowCreateMessage* windowCreateMsg = new ogunWindowCreateMessage();
        // ogunWindowCreateResponseMessage* windowCreateResponseMsg = new ogunWindowCreateResponseMessage();

        // // send initial window creation message to window manager
        // header.id = 1000;
        // data.name = "hesabu window";
        // data.height = 800;
        // data.width = 600;
        // data.mode = hesabu::HWindowMode::NORMAL;
        // windowCreateMsg->populate(header, data);
        // windowCreateMsg->arm();
        // // send(windowCreateMsg);
        
        // // wait for window manager create window response
        // while(recv(windowCreateResponseMsg))
        // {
            m_bWindowCreated = true;
        // }

        // temp receive message time delay simulate
        std::this_thread::sleep_for(std::chrono::seconds(3));

        if (!(m_bVulkanInitialized && m_bWindowCreated))
        {
            std::string name = "hesabu window";
            //     FindWindow(data.name);
            // VulkanModelInfo info;
            HWND hwnd = FindWindow(name.c_str(), 0);
            HMODULE hModule = GetModuleHandle(NULL);
            // LPDWORD* lpdwProcessId = 0;
            DWORD result = GetWindowThreadProcessId(
                hwnd, NULL
              );

              HWINEVENTHOOK ehook = SetWinEventHook(
                EVENT_MIN,
                EVENT_MAX,
                hModule,
                HandleWinEvent,
                0,
                0,
                WINEVENT_OUTOFCONTEXT
              );

            // HWND hwnd; 
            BOOL fDone; 
            MSG msg; 
            
            BOOL bRet;

            // Begin the operation and continue until it is complete 
            // or until the user clicks the mouse or presses a key. 
            fDone = FALSE; 
            while (!fDone) 
            { 
                // fDone = DoLengthyOperation(); // application-defined function 

                // Remove any messages that may be in the queue. If the 
                // queue contains any mouse or keyboard 
                // messages, end the operation. 

                while (bRet = PeekMessage(&msg, hwnd,  0, 0, PM_REMOVE))
                // while (bRet = GetMessage(&msg, hwnd,  0, 0))
                { 
                    switch(msg.message) 
                    { 
                        case WM_LBUTTONDOWN: 
                            std::cout << "EXECUTOR THREAD WM_LBUTTONDOWN"<< std::endl;
                        case WM_RBUTTONDOWN: 
                            std::cout << "EXECUTOR THREAD WM_RBUTTONDOWN"<< std::endl;
                        case WM_KEYDOWN: 
                            // 
                            // Perform any required cleanup. 
                            // 
                            fDone = TRUE; 
                    }
                }
            }

            // info.window.name = data.name;
            // info.window.height = data.height;
            // info.window.width = data.width;
            // info.shaderLibraryPath = "D:/dev/projects_v1.0.0/ogun/assets/shaders";
            // m_model->init(info);
        }
    }
}

void VOgunExecutor::update()
{
    static auto startTime = std::chrono::high_resolution_clock::now();
    auto currentTime = std::chrono::high_resolution_clock::now();
    float tick = std::chrono::duration<float, std::chrono::seconds::period>(currentTime - startTime).count();
    // m_model->draw(tick);
}

void VOgunExecutor::pause()
{

}

void VOgunExecutor::reset()
{

}

void VOgunExecutor::shutdown()
{
//    m_model->shutdown();
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


void testModel()
{
    std::cout << "run test kernel model" << std::endl;
    std::thread windowManagerThread(runWindowManager);
    // std::thread vulkanExecutorThread(runVulkanExecutor);
    // std::thread sceneManagerThread(runSceneManager);
    // std::thread dataArbiterServerThread(runDataArbiterServer);

    glm::vec3 testvector(1, 3, 4);
    std::cout << "test vector " << testvector.x << " " << testvector.y << " " << testvector.z << std::endl;

    windowManagerThread.join();
    // vulkanExecutorThread.join();
    // sceneManagerThread.join();
    // dataArbiterServerThread.join();
}


int main(int argc, char* argv[])
{
    testModel();
    return 0;
}
