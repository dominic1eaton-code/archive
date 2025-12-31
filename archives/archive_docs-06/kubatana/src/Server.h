/**
 * @brief
 * @note
 */
#ifndef SERVER_H
#define SERVER_H

#include <string>

namespace kubatana
{

class Server
{
public:
    Server() = default;
    virtual ~Server(void) = default;
    virtual void init() = 0;
    virtual void configure() = 0;
    virtual void start() = 0;
    virtual void stop() = 0;

protected:
    uint32_t m_id;
    uint32_t m_port;
    std::string m_name;
    std::string m_ipAddress;
    const std::string DEFAULT_NAME = "server";
    const std::string DEFAULT_IP_ADDRESS = "127.0.0.1";
    const uint32_t DEFAULT_PORT = 80;
};

}; // namespace kubatana

#endif // SERVER_H