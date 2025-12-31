/**
 * @header DEFAULT
 * @brief
 * @note 
 */
#undef UNICODE
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <winsock2.h>
#include <ws2tcpip.h>
#include <stdlib.h>
#include <stdio.h>
#include <string>
#include <iostream>
#include <fstream>
#include <stdexcept>
#include <sstream>
#include <random>
#include <thread>
#pragma comment (lib, "Ws2_32.lib")
#pragma comment (lib, "Mswsock.lib")
#pragma comment (lib, "AdvApi32.lib")


// void Call(int ID)
// {
//     std::cout << "Created new thread with ID: " << ID <<  std::endl;
// }

// void Call()
// {
//     std::random_device rd; // obtain a random number from hardware
//     std::mt19937 gen(rd()); // seed the generator
//     std::uniform_int_distribution<> distr(0, 100); // define the range
//     int threadID = distr(gen);
//     std::cout << "Created new thread with ID: " << threadID <<  std::endl;
// }

namespace
{
    const uint32_t DEFAULT_BUFLEN = 512;
    const uint32_t MAX_CLIENTS = 50;

    struct Server
    {
        SOCKET socket;
        SOCKADDR_IN networkAddress;
        const char* ipaddress;
        uint16_t port;
        uint32_t status;
    };
    
    struct Clients
    {
        Clients()
            : bHasThread(false)
            , bConnected(false)
            , active(false)
            , established(false)
        {}

        bool bHasThread;
        bool bConnected;
        bool active;
        bool established;
        SOCKET socket;
    };
    Clients clients[MAX_CLIENTS];

    struct Message
    {
        Message()
            : result(0)
        {}

        int result;
        char buffer[DEFAULT_BUFLEN];
        int bufferlen = DEFAULT_BUFLEN;
    };
}


std::string handleRequest()
{
    std::string response = "HTTP/1.1 200 Okay\r\n";
    // std::string header = "Server: Crude Server\r\nContent-Type: text/html\r\n";
    std::string header = "Content-Type: text/html; charset=ISO-8859-4\r\n\r\n";
    // std::string body = "<html><head><title>Title of the document</title></head><body><h1>This is a heading</h1><p>This is a paragraph.</p></body></html>";
    std::string blankline = "\r\n";

    // read from html file
    std::string defaultBody = "</html><h1>NO CONTENT TO DISPLAY</h1></html>";
    std::string body = "";
    std::ifstream indexPageFile("index.html");
    if (indexPageFile.is_open())
    {
        // char character;
        std::string line;
        while (indexPageFile)
        {
            // character = indexPageFile.get();
            std::getline(indexPageFile, line);
            body += line;
        }
    }

    if (body.empty())
    {
        body = defaultBody;
    }

    return response + header + blankline + body;
    // return "HTTP/1.1 200\r\n\r\nContent-Type: text/html\r\n\r\n<h1>Hey, 42!</h1>\n";
    // std::string message = response + header + blankline + body;
    // const char* msg = message.c_str();
    // requestData = (char*)msg;
    // requestData = strcat(response, header);
    // return "HTTP/1.1 200 Okay\r\nContent-Type: text/html; charset=ISO-8859-4\r\n\r\n<h1>Hello, client! Welcome to the Virtual Machine Web..</h1>";
    // return ;
}


void connectionRequest(SOCKET csocket)
{
    uint32_t rstatus = 0;
    uint32_t sstatus = 0;
    Message responseMessage;
    bool established = false;

    // // Receive until the peer shuts down the connection
    // if (established == false)
    // {
    // send html data
    std::string htmlRequestMessage = handleRequest();
    std::cout << "Sending initial HTML message of size " << htmlRequestMessage.length() << std::endl;
    sstatus = send(csocket, htmlRequestMessage.c_str(), strlen(htmlRequestMessage.c_str()), NULL);
    if (sstatus == SOCKET_ERROR)
    {
        printf("send failed with error: %d\n", WSAGetLastError());
        closesocket(csocket);
        WSACleanup();
    }
    printf("Bytes sent: %d\n", sstatus);
    
    Sleep(10);
    rstatus = recv(csocket, responseMessage.buffer, responseMessage.bufferlen, NULL);
    if (rstatus > 0)
    {
        printf("Bytes received: %d\n", rstatus);
        std::cout << "received message: " << responseMessage.buffer << std::endl;
    }
    
    // Sleep(10);
    closesocket(csocket);
    established = true;
    // }
}

int startHTTPServer(Server* server, const char* port, const char* ipaddress)
{
    uint32_t status = 0;

    // server properties
    WSADATA m_wsaData;
    SOCKET m_socket = INVALID_SOCKET;
    Message sendMessage;
    Message recieveMessage;
    struct addrinfo* m_result = NULL;
    struct addrinfo m_hints;

    // Initialize Winsock
    status = WSAStartup(MAKEWORD(2,2), &m_wsaData);
    if (status != 0)
    {
        printf("WSAStartup failed with error: %d\n", status);
        return 1;
    }

    // defaults
    ZeroMemory(&m_hints, sizeof(m_hints));
    m_hints.ai_family = AF_INET;
    m_hints.ai_socktype = SOCK_STREAM;
    m_hints.ai_protocol = IPPROTO_TCP;
    m_hints.ai_flags = AI_PASSIVE;

    // Resolve the server address and port
    status = getaddrinfo(NULL, port, &m_hints, &m_result);
    if (status != 0)
    {
        printf("getaddrinfo failed with error: %d\n", status);
        WSACleanup();
        return 1;
    }

    // Create a SOCKET for the server to listen for client connections.
    m_socket = socket(
        m_result->ai_family,
        m_result->ai_socktype,
        m_result->ai_protocol);
    if (m_socket == INVALID_SOCKET)
    {
        printf("socket failed with error: %ld\n", WSAGetLastError());
        freeaddrinfo(m_result);
        WSACleanup();
        return 1;
    }
    server->socket = m_socket;

    // create server network info struct
    uint16_t m_port = (uint16_t) strtoul(port, NULL, 0);
    SOCKADDR_IN serverAddress;
    serverAddress.sin_family = AF_INET;
    serverAddress.sin_addr.s_addr = inet_addr(ipaddress);
    serverAddress.sin_port =  htons(m_port);
    server->networkAddress = serverAddress;

    // bind to server socket
    status = bind(
        m_socket,
        (sockaddr*)&serverAddress,
        sizeof(serverAddress));
    if (status == SOCKET_ERROR)
    {
        printf("bind failed with error: %d\n", WSAGetLastError());
        freeaddrinfo(m_result);
        closesocket(m_socket);
        WSACleanup();
        return 1;
    }
    freeaddrinfo(m_result);

    // listen for connections
    status = listen(m_socket, SOMAXCONN);
    if (status == SOCKET_ERROR)
    {
        printf("listen failed with error: %d\n", WSAGetLastError());
        closesocket(m_socket);
        WSACleanup();
        return 1;
    }

    // set server blocking state
    u_long blocking = 0;
    ioctlsocket(m_socket, FIONBIO, &blocking);
    if (status == SOCKET_ERROR)
    {
        printf("listen failed with error: %d\n", WSAGetLastError());
        closesocket(m_socket);
        WSACleanup();
    }

    server->status = status;
    return 0;
}

int runHTTPServer(uint8_t ID, uint16_t port, const char* ipaddress)
{
    uint32_t status = 0;

    // server properties
    Server server;
    const char* DEFAULT_PORT = "80";

    // initialize the server
    server.port = port;
    server.ipaddress = ipaddress;
    startHTTPServer(&server, DEFAULT_PORT, ipaddress);

    // main server loop
	// const char sendMessage[DEFAULT_BUFLEN] = "This TEST message 0 being displayed to you in your Browser.\nIs sent from a C++ Winsock HTTP Server.\n Now Closing Connection.\r";
    const char sendMessage[DEFAULT_BUFLEN] = "Established connection to browser client\r\n";
    Message responseMessage;
    bool bRunning = true;
    uint32_t clientsIndex = 0;
    int32_t networkAddresslen;
    SOCKET m_clientsocket;
    std::string serverMessage;
    bool active = false;
    bool established = false;
    while(bRunning)
    {
        // if (active == false)
        if (clients[clientsIndex].active == false)
        {
        // if (clients[clientsIndex].bConnected == false)
        // {
            // accept client connections
            networkAddresslen = sizeof(server.networkAddress);
            m_clientsocket = accept(server.socket, (struct sockaddr*)&server.networkAddress, &networkAddresslen);

            if (m_clientsocket == SOCKET_ERROR)
            {
                printf("accept failed with error: %d\n", WSAGetLastError());
                closesocket(server.socket);
                WSACleanup();
                return 1;
            }
            else if (m_clientsocket == INVALID_SOCKET)
            {
                printf("accept received invalid socket with status: %d\n", WSAGetLastError());
            }
            else // (m_clientsocket != INVALID_SOCKET)
            {
                clients[clientsIndex].socket = m_clientsocket;
                clients[clientsIndex].bConnected = true;
                clients[clientsIndex].bHasThread = false;
                clientsIndex++;
                std::cout << "New client connected: " << m_clientsocket << std::endl;
            }

            // delay
            Sleep(1);
            // active = true;
            clients[clientsIndex].active = true;
        // }
        }
        
        // receieve/send data from clients
        if (clientsIndex)
        {
            // iterate through active clients
            for (int clientIndex = 0; clientIndex < clientsIndex; clientIndex++)
            {
                // establish communication channel
                // if (established == false)
                // if (clients[clientsIndex].established == false)
                if (clients[clientIndex].bConnected)
                {
                    // Create new thread to interact with new client
                    if (clients[clientIndex].bHasThread == false)
                    {
                        // create new connection thread
                        std::thread connectRequestThread(connectionRequest, clients[clientIndex].socket);
                        connectRequestThread.join();
                        clients[clientIndex].bHasThread = true;
                    }
                    // // Send Client a Message
                    // std::cout << "Sending initial message" << std::endl;
                    // status = send(clients[clientIndex].socket, sendMessage, strlen(sendMessage), NULL);

                    // // Receive client reply, if any
                    // Sleep(10);
                    // recv(clients[clientIndex].socket, responseMessage.buffer, responseMessage.bufferlen, NULL);
                    // std::cout << "received message: " << responseMessage.buffer << std::endl;

                    // // send html data
                    // std::string htmlRequestMessage = handleRequest();
                    // std::cout << "Sending initial HTML message of size " << htmlRequestMessage.length() << std::endl;
                    // status = send(clients[clientIndex].socket, htmlRequestMessage.c_str(), strlen(htmlRequestMessage.c_str()), NULL);

                    // // char msg[] = "HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nContent-length: 20\r\n\r\n<html><h1>Hello World</h1></html>";
                    // // std::cout << "Sending initial HTML message" << msg << std::endl;
                    // // status = send(clients[clientIndex].socket, msg, strlen(msg), NULL);

                    // Sleep(10);
                    // recv(clients[clientIndex].socket, responseMessage.buffer, responseMessage.bufferlen, NULL);
                    // std::cout << "received message: " << responseMessage.buffer << std::endl;

                    // established = true;
                    // clients[clientsIndex].established = true;

                    // close socket when done sending
                    // closesocket(server.socket);
                    // closesocket(clients[clientIndex].socket);
                }
                
                // get server user input
                Sleep(10);
                std::cout << "Enter message to server: ";
                std::getline(std::cin, serverMessage);
                std::cout << std::endl;
                if (strcmp(serverMessage.c_str(), "disconnect") == 0)
                {
                    std::cout << "closing connection..." << std::endl;
                    // closesocket(clients[clientIndex].socket);
                    closesocket(server.socket);
                }

                if (strcmp(serverMessage.c_str(), "stop") == 0)
                {
                    std::cout << "stopping server..." << std::endl;
                    bRunning = false;
                }
                
        //         memset(&receiveMessage.buffer, 0, receiveMessage.bufferlen);
        //         if (clients[clientIndex].bConnected)
        //         {
        //             if (clients[clientIndex].bHasThread == false)
        //             {
        //                 // create new connection thread
        //                 // std::thread connectRequestThread(connectRequest, clients[clientIndex].socket, m_recvbuf, m_recvbuflen, m_iresult, m_isendResult);
        //                 // connectRequestThread.join();
        //                 // clients[clientIndex].bHasThread = true;
        //             }
        //         }
            }
        }
    }

    system("pause");
    WSACleanup();
    // getchar(); // pause program until user input
    // system("pause");
    return status;
}

int runHTTPClient(uint8_t ID, uint16_t port, const char* ipaddress)
{
    uint32_t status = 0;
    return status;
}

int main(int argc, char* argv[])
{
    std::cout << "Hello App1 main thread ! " << std::endl;

    // server configuration
    std::random_device rd; // obtain a random number from hardware
    std::mt19937 gen(rd()); // seed the generator
    std::uniform_int_distribution<> distr(0, 100); // define the range
    int serverID = distr(gen);

    // runHTTPServer(serverID, 80, "0.0.0.0");
    runHTTPServer(serverID, 80, "192.168.1.25");
    // std::thread client0Thread(Call);
    // std::thread client1Thread(Call);
    // std::thread serverThread(Call);
    // client0Thread.join();
    // client1Thread.join();
    // serverThread.join();
    return 0;
}