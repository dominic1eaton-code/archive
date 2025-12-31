/**
 * @header DEFAULT
 * @brief
 * @note 
 */
#include <iostream>
#include <unordered_map>
#include <string>
#include <queue>
#include <vector>
#include <thread>
#include <mutex>
#include <condition_variable>
#include <chrono>

using namespace std;

class Subscriber; // Forward declaration

class Message {
public:
    // Message(string data) : m_data(data) {}
    Message(string header, string data) : m_header(header), m_data(data) {}
    string header() const { return m_header; }
    string data() const { return m_data; }
private:
    string m_header;
    string m_data;
};

class Broker {
    unordered_map<string, queue<Message*>> topics;
    unordered_map<string, vector<Subscriber*>> subscribers;
    mutex mutex_;
    condition_variable cond_;
public:
    void subscribe(const string &topic, Subscriber *sub);
    void publish(const string &topic, Message *message);
    void processMessages();
};

class Publisher {
    Broker *broker;
public:
    Publisher(Broker &broker) : broker(&broker) {}
    void publish(const string &topic, Message *message) {
        broker->publish(topic, message);
    }
};
 
class Subscriber {
    Broker *broker;
    // std::vector<std::string> m_messages;
public:
    // Subscriber() : m_messages({}) {}
    // std::vector<Message> messages() const { return m_messages; }
    Subscriber(Broker &broker) : broker(&broker) {}
    void subscribe(const string &topic) {
        broker->subscribe(topic, this);
    }
    void receive(const Message *message, const string &topic) {
        cout << "Received message: " << message->data() << ", from topic: " << topic << endl;
        // Message msg(message->header(), message->data()) ;
        // m_messages.push_back("test");
    }
};

void Broker::subscribe(const string &topic, Subscriber *sub) {
    lock_guard<mutex> lock(mutex_);
    subscribers[topic].push_back(sub);
}

void Broker::publish(const string &topic, Message *message) {
    {
        lock_guard<mutex> lock(mutex_);
        topics[topic].push(message);
    }
    cond_.notify_all();

    // std::this_thread::sleep_for(std::chrono::seconds(1));
    // {
    //     std::lock_guard<std::mutex> lk(mutex_);
    //     std::cerr << "Notifying...\n";
    // }
    // cond_.notify_all();
 
    // std::this_thread::sleep_for(std::chrono::seconds(1));
 
    // {
    //     std::lock_guard<std::mutex> lk(mutex_);
    //     // i = 1;
    //     std::cerr << "Notifying again...\n";
    // }
    // cond_.notify_all();
}

void Broker::processMessages() {
    unique_lock<mutex> lock(mutex_);
    while (true) {
        cond_.wait(lock, [this]{
            for (const auto &topic : topics) {
                if (!topic.second.empty()) {
                    return true;
                }
            }
            return false;
        });
        for (auto &topic : topics) {
            string topic_name = topic.first;
            queue<Message*> &q = topic.second;
            while (!q.empty()) {
                Message *m = q.front();
                q.pop();
                vector<Subscriber*> &subs = subscribers[topic_name];
                for (auto &sub : subs) {
                    sub->receive(m, topic_name);
                }
            }
        }
    }
}

std::chrono::seconds duration(1);

// void comp0thread(Broker& broker)
void comp0thread(Broker& broker)
{
    std::this_thread::sleep_for( std::chrono::seconds (2) );

    Publisher vexport(broker);
    Subscriber import(broker);
    
    import.subscribe("sharedMessage3");
    
    Message* sharedMessage0 = new Message("sharedMessage0", "Comp0 message 0000");

    // import.subscribe(sharedMessage0->header());
    vexport.publish(sharedMessage0->header(), sharedMessage0);

    
    Message* sharedMessage1 = new Message("sharedMessage1", "Comp0 message 1111");

    vexport.publish(sharedMessage1->header(), sharedMessage1);

    std::this_thread::sleep_for(std::chrono::seconds(1));
    {
        vexport.publish("sharedMessage1", new Message("sharedMessage1", "Comp0 message 1111 2222"));
    }
    
    std::this_thread::sleep_for(std::chrono::seconds(1));
    {
        vexport.publish("sharedMessage1", new Message("sharedMessage1", "Comp0 message 1111 3333"));
    }

    // std::this_thread::sleep_for(std::chrono::seconds(5));
    // {
    //     std::vector<const Message*> messages = import.messages();
    // }
}

void comp1thread(Broker& broker)
{
    // std::this_thread::sleep_for( duration );

    Publisher vexport(broker);
    Subscriber import(broker);

    import.subscribe("sharedMessage0");
    import.subscribe("sharedMessage1");
    // export.publish(sharedMessage0->header(), sharedMessage0);

    std::this_thread::sleep_for(std::chrono::seconds(5));
    {
        vexport.publish("sharedMessage3", new Message("sharedMessage1", "Comp1 message 3333 0000"));
    }

}

// void testthread()
// {
//     Broker broker;

//     Publisher pub(broker);
//     Subscriber sub1(broker), sub2(broker);

//     sub1.subscribe("A");
//     sub2.subscribe("A");

//     thread t(&Broker::processMessages, &broker);

//     pub.publish("A", new Message("Hello, Topic A!"));
//     pub.publish("A", new Message("Hello, another topic a message"));

//     t.join();
// }

int main() 
{
    Broker broker;

    thread c0(comp0thread, std::ref(broker));
    thread c1(comp1thread, std::ref(broker));

    c0.join();
    c1.join();

    thread t(&Broker::processMessages, &broker);
    t.join();
    return 0;
}

 
// std::condition_variable cv;
// std::mutex cv_m; // This mutex is used for three purposes:
//                  // 1) to synchronize accesses to i
//                  // 2) to synchronize accesses to std::cerr
//                  // 3) for the condition variable cv
// int i = 0;
 
// void waits()
// {
//     std::unique_lock<std::mutex> lk(cv_m);
//     std::cerr << "Waiting... \n";
//     cv.wait(lk, []{ return i == 1; });
//     std::cerr << "...finished waiting. i == 1\n";
// }
 
// void signals()
// {
//     std::this_thread::sleep_for(std::chrono::seconds(1));
//     {
//         std::lock_guard<std::mutex> lk(cv_m);
//         std::cerr << "Notifying...\n";
//     }
//     cv.notify_all();
 
//     std::this_thread::sleep_for(std::chrono::seconds(1));
 
//     {
//         std::lock_guard<std::mutex> lk(cv_m);
//         i = 1;
//         std::cerr << "Notifying again...\n";
//     }
//     cv.notify_all();
// }
 
// int main()
// {
//     std::thread t1(waits), t2(waits), t3(waits), t4(signals);
//     t1.join(); 
//     t2.join(); 
//     t3.join();
//     t4.join();
// }