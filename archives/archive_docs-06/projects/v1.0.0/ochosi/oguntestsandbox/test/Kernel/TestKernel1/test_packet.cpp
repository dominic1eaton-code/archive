
/**
 * @header DEFAULT
 * @brief
 * @note 
 */// https://www.google.com/search?client=firefox-b-1-d&q=c%2B%2B+packet+class
#include <iostream>
#include <vector>

class Packet {
public:
    // Constructor
    Packet(int sequenceNumber, const std::vector<unsigned char>& data) : 
        sequenceNumber_(sequenceNumber), data_(data) {}

    // Getters
    int getSequenceNumber() const { return sequenceNumber_; }
    const std::vector<unsigned char>& getData() const { return data_; }

    // Setters (if needed)
    void setSequenceNumber(int sequenceNumber) { sequenceNumber_ = sequenceNumber; }
    void setData(const std::vector<unsigned char>& data) { data_ = data; }

    // Method to serialize the packet into a byte stream
    std::vector<unsigned char> serialize() const {
        std::vector<unsigned char> buffer;

        // Add sequence number (assuming 4 bytes)
        buffer.push_back((sequenceNumber_ >> 24) & 0xFF);
        buffer.push_back((sequenceNumber_ >> 16) & 0xFF);
        buffer.push_back((sequenceNumber_ >> 8) & 0xFF);
        buffer.push_back(sequenceNumber_ & 0xFF);

        // Add data size (assuming 4 bytes)
        int dataSize = data_.size();
        buffer.push_back((dataSize >> 24) & 0xFF);
        buffer.push_back((dataSize >> 16) & 0xFF);
        buffer.push_back((dataSize >> 8) & 0xFF);
        buffer.push_back(dataSize & 0xFF);

        // Add data
        buffer.insert(buffer.end(), data_.begin(), data_.end());

        return buffer;
    }

    // Method to deserialize a byte stream into a packet
    static Packet deserialize(const std::vector<unsigned char>& buffer) {
        int sequenceNumber = (buffer[0] << 24) | (buffer[1] << 16) | (buffer[2] << 8) | buffer[3];
        int dataSize = (buffer[4] << 24) | (buffer[5] << 16) | (buffer[6] << 8) | buffer[7];
        std::vector<unsigned char> data(buffer.begin() + 8, buffer.begin() + 8 + dataSize);

        return Packet(sequenceNumber, data);
    }

private:
    int sequenceNumber_;
    std::vector<unsigned char> data_;
};





class Message
{

};


struct ogunWindowStateMessageData
{

    HWND m_hwnd;

    std::string m_name;

    uint32_t m_width;

    uint32_t m_height;
};


class ogunWindowStateMessage : Message
{
public:

    ogunWindowStateMessage()
        : m_hwnd(nullptr)
        , m_name("")
        , m_width(600)
        , m_height(800)
    {}

    ogunWindowStateMessage()
        : m_hwnd(nullptr)
        , m_name("")
        , m_width(600)
        , m_height(800)
    {}

    virtual ~ogunWindowStateMessage(void) = default;

    ogunWindowStateMessage(ogunWindowStateMessage& msg) 
    {
        m_hwnd = msg.hwnd();
        m_name = msg.name();
        m_width = msg.width();
        m_height = msg.height();
    }

    HWND hwnd() const { return m_hwnd; }

    std::string  name() const { return m_name; }

    uint32_t width() const { return m_width; }

    uint32_t height() const { return m_height; }

private:

    
};

