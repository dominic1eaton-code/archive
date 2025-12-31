/**
 * @brief
 * @note
 */
#ifndef TCPServer_H
#define TCPServer_H

#include "Server.h"

namespace kubatana
{

class TCPServer : public Server
{
public:
    TCPServer() = default;
    virtual ~TCPServer(void) = default;
    void init();
    void configure();
    void start();
    void stop();
};

class Win32TCPServer : public Server
{
public:
    Win32TCPServer() = default;
    virtual ~Win32TCPServer(void) = default;
    void init();
    void configure();
    void start();
    void stop();
};

}; // namespace kubatana

#endif // TCPServer_H