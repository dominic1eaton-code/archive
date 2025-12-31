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

};

void VWindowManager::initialize()
{

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
    data.name = "OgunEngine";
    std::wstring widestr = std::wstring(data.name.begin(), data.name.end());
    hesabu::HWindow* window = new hesabu::HWindow();
    window->create(widestr.c_str());
    // window->init();
    window->show();
    window->message();
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

void testModel()
{
    std::cout << "run test kernel model" << std::endl;
    std::thread windowManagerThread(runWindowManager);
    windowManagerThread.join();
}

int main(int argc, char* argv[])
{
    testModel();
    return 0;
}
