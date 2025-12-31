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
#include <stdexcept>
#include <sstream>
#include <random>
#include <thread>
#pragma comment (lib, "Ws2_32.lib")
#pragma comment (lib, "Mswsock.lib")
#pragma comment (lib, "AdvApi32.lib")

// forward declarations and constants
// #define DEAFULT_PORT 27105
// #define DEFAULT_BUFLEN 512
#define MAX_CLIENTS 50

struct Clients
{
    bool bHasThread;
    bool bConnected;
    SOCKET socket;
};

Clients clients[MAX_CLIENTS];



int runWindowsServer(int id)
{
    std::cout << "Running Server " << std::endl;

    // data to send
    // const char* m_sendbuf = "this is a test from client ";
    std::string m_sendbufHeader = "this is a message reciept from server with ID: ";
    std::stringstream sbuf;
    sbuf << m_sendbufHeader << id;
    std::string sendbuf = sbuf.str();
    const char* m_sendbuf = sendbuf.c_str();
    std::cout << "Server message: " << m_sendbuf << std::endl;

    // constants
    const CHAR* DEFAULT_PORT = "27015";
    const int DEFAULT_BUFLEN = 512;

    // init properties
    WSADATA m_wsaData;
    int m_iresult;
    SOCKET m_serverSocket = INVALID_SOCKET;
    SOCKET m_clientSocket = INVALID_SOCKET;
    struct addrinfo* m_result = NULL;
    struct addrinfo m_hints;
    int m_isendResult;
    char m_recvbuf[DEFAULT_BUFLEN];
    int m_recvbuflen = DEFAULT_BUFLEN;

    // Initialize Winsock
    m_iresult = WSAStartup(MAKEWORD(2,2), &m_wsaData);
    if (m_iresult != 0)
    {
        printf("WSAStartup failed with error: %d\n", m_iresult);
        return 1;
    }

    // defaults
    ZeroMemory(&m_hints, sizeof(m_hints));
    m_hints.ai_family = AF_INET;
    m_hints.ai_socktype = SOCK_STREAM;
    m_hints.ai_protocol = IPPROTO_TCP;
    m_hints.ai_flags = AI_PASSIVE;

    // Resolve the server address and port
    m_iresult = getaddrinfo(NULL, DEFAULT_PORT, &m_hints, &m_result);
    if (m_iresult != 0)
    {
        printf("getaddrinfo failed with error: %d\n", m_iresult);
        WSACleanup();
        return 1;
    }

    // Create a SOCKET for the server to listen for client connections.
    m_serverSocket = socket(
        m_result->ai_family,
        m_result->ai_socktype,
        m_result->ai_protocol);
    if (m_serverSocket == INVALID_SOCKET) {
        printf("socket failed with error: %ld\n", WSAGetLastError());
        freeaddrinfo(m_result);
        WSACleanup();
        return 1;
    }

    // Setup the TCP listening socket
    m_iresult = bind(
        m_serverSocket, 
        m_result->ai_addr, 
        (int)m_result->ai_addrlen);
    if (m_iresult == SOCKET_ERROR)
    {
        printf("bind failed with error: %d\n", WSAGetLastError());
        freeaddrinfo(m_result);
        closesocket(m_serverSocket);
        WSACleanup();
        return 1;
    }
    freeaddrinfo(m_result);

    m_iresult = listen(m_serverSocket, SOMAXCONN);
    if (m_iresult == SOCKET_ERROR)
    {
        printf("listen failed with error: %d\n", WSAGetLastError());
        closesocket(m_serverSocket);
        WSACleanup();
        return 1;
    }

    // Accept a client socket
    m_clientSocket = accept(m_serverSocket, NULL, NULL);
    if (m_clientSocket == INVALID_SOCKET)
    {
        printf("accept failed with error: %d\n", WSAGetLastError());
        closesocket(m_serverSocket);
        WSACleanup();
        return 1;
    }

    // No longer need server socket
    closesocket(m_serverSocket);

    // Receive until the peer shuts down the connection
    do {
        m_iresult = recv(m_clientSocket, m_recvbuf, m_recvbuflen, 0);
        if (m_iresult > 0)
        {
            printf("Bytes received: %d\n", m_iresult);

            // Echo the buffer back to the sender
            m_isendResult = send(m_clientSocket, m_recvbuf, m_iresult, 0 );
            if (m_isendResult == SOCKET_ERROR)
            {
                printf("send failed with error: %d\n", WSAGetLastError());
                closesocket(m_clientSocket);
                WSACleanup();
                return 1;
            }
            printf("Bytes sent: %d\n", m_isendResult);

            // int sbyteCount = send(m_clientSocket, m_sendbuf, m_iresult, 0);
            // if (sbyteCount == SOCKET_ERROR)
            // {
            //     std::cout << "Server send error: " << WSAGetLastError() << std::endl;
            //     return 1;
            // }
            // else
            // {
            //     std::cout << "Server: Sent " << sbyteCount << " bytes" << std::endl;
            // }
        }
        else if (m_iresult == 0)
        {
            printf("Connection closing...\n");
        }
        else 
        {
            printf("recv failed with error: %d\n", WSAGetLastError());
            closesocket(m_clientSocket);
            WSACleanup();
            return 1;
        }
    } while (m_iresult > 0);
    // } while(true);

    // shutdown the connection since we're done
    m_iresult = shutdown(m_clientSocket, SD_SEND);
    if (m_iresult == SOCKET_ERROR)
    {
        printf("shutdown failed with error: %d\n", WSAGetLastError());
        closesocket(m_clientSocket);
        WSACleanup();
        return 1;
    }

    // cleanup
    closesocket(m_clientSocket);
    WSACleanup();

    return 0;
}

int runWindowsClient(int id, const char* serverIP)
{
    std::cout << "Running Client" << std::endl;

    // data to send
    // const char* m_sendbuf = "this is a test from client ";
    std::string m_sendbufHeader = "this is a test from client with ID: ";
    std::stringstream sbuf;
    sbuf << m_sendbufHeader << id;
    std::string sendbuf = sbuf.str();
    const char* m_sendbuf = sendbuf.c_str();

    std::cout << "Client message: " << m_sendbuf << std::endl;
    std::cout << "server IP address: " << serverIP << std::endl;

    // constants
    const CHAR* DEFAULT_PORT = "27015";
    const int DEFAULT_BUFLEN = 512;

    // init properties
    WSADATA m_wsaData;
    int m_iresult;
    SOCKET m_clientSocket = INVALID_SOCKET;
    struct addrinfo* m_result = NULL;
    struct addrinfo* m_ptr = NULL;
    struct addrinfo m_hints;
    int m_isendResult;
    char m_recvbuf[DEFAULT_BUFLEN];
    int m_recvbuflen = DEFAULT_BUFLEN;

    // Initialize Winsock
    m_iresult = WSAStartup(MAKEWORD(2,2), &m_wsaData);
    if (m_iresult != 0)
    {
        printf("WSAStartup failed with error: %d\n", m_iresult);
        return 1;
    }

    ZeroMemory(&m_hints, sizeof(m_hints) );
    m_hints.ai_family = AF_UNSPEC;
    m_hints.ai_socktype = SOCK_STREAM;
    m_hints.ai_protocol = IPPROTO_TCP;

    // Resolve the server address and port
    m_iresult = getaddrinfo(serverIP, DEFAULT_PORT, &m_hints, &m_result);
    if (m_iresult != 0)
    {
        printf("getaddrinfo failed with error: %d\n", m_iresult);
        WSACleanup();
        return 1;
    }

    // Attempt to connect to an address until one succeeds
    for(m_ptr = m_result; m_ptr != NULL; m_ptr = m_ptr->ai_next)
    {
        // Create a SOCKET for connecting to server
        m_clientSocket = socket(
            m_ptr->ai_family,
            m_ptr->ai_socktype,
            m_ptr->ai_protocol);
        if (m_clientSocket == INVALID_SOCKET)
        {
            printf("socket failed with error: %ld\n", WSAGetLastError());
            WSACleanup();
            return 1;
        }

        // Connect to server.
        m_iresult = connect(
            m_clientSocket,
            m_ptr->ai_addr,
            (int)m_ptr->ai_addrlen);
        if (m_iresult == SOCKET_ERROR) {
            closesocket(m_clientSocket);
            m_clientSocket = INVALID_SOCKET;
            continue;
        }
        break;
    }
    freeaddrinfo(m_result);
    if (m_clientSocket == INVALID_SOCKET)
    {
        printf("Unable to connect to server!\n");
        WSACleanup();
        return 1;
    }

    // send/receive data
    int loopthis = 1;
    std::string sendbuf2;
    while (loopthis == 1)
    {
        std::cout << "Type to say: ";
        std::getline(std::cin, sendbuf2);
        std::cout << std::endl;

        // Send an initial buffer
        m_iresult = send(m_clientSocket, sendbuf2.c_str(),
        (int)strlen(sendbuf2.c_str()), 0);

        if (m_iresult == SOCKET_ERROR)
        {
            printf("send failed with error: %d\n", WSAGetLastError());
            closesocket(m_clientSocket);
            WSACleanup();
            return 1;
        }

        printf("Bytes Sent: %ld\n", m_iresult);
        if (strcmp(sendbuf2.c_str(), "break") == 0)
        {
            std::cout << "exiting...\n";
            loopthis = 0;
            break;
        }
    }

    // shutdown the connection since no more data will be sent
    m_iresult = shutdown(m_clientSocket, SD_SEND);
    if (m_iresult == SOCKET_ERROR)
    {
        printf("shutdown failed with error: %d\n", WSAGetLastError());
        closesocket(m_clientSocket);
        WSACleanup();
        return 1;
    }

    // Receive until the peer closes the connection
    do
    {
        m_iresult = recv(m_clientSocket, m_recvbuf, m_recvbuflen, 0);
        if (m_iresult > 0)
        {
            printf("Bytes received: %d\n", m_iresult);
        }
        else if (m_iresult == 0)
        {
            printf("No data received \n");
        }
        else
        {
            printf("recv failed with error: %d\n", WSAGetLastError());
        }
        Sleep(3000);
    } while(m_iresult > 0);


    // Send an initial buffer
    // m_iresult = send(
    //     m_clientSocket, 
    //     m_sendbuf, 
    //     (int)strlen(m_sendbuf),
    //     0);

    // if (m_iresult == SOCKET_ERROR)
    // {
    //     printf("send failed with error: %d\n", WSAGetLastError());
    //     closesocket(m_iresult);
    //     WSACleanup();
    //     return 1;
    // }
    // printf("Bytes Sent: %ld\n", m_iresult);

    // // shutdown the connection since no more data will be sent
    // m_iresult = shutdown(m_clientSocket, SD_SEND);
    // if (m_iresult == SOCKET_ERROR)
    // {
    //     printf("shutdown failed with error: %d\n", WSAGetLastError());
    //     closesocket(m_clientSocket);
    //     WSACleanup();
    //     return 1;
    // }

    // // Receive until the peer closes the connection
    // do
    // {
    //     m_iresult = recv(m_clientSocket, m_recvbuf, m_recvbuflen, 0);
    //     if ( m_iresult > 0 )
    //     {            
    //         printf("Bytes received: %d\n", m_iresult);
    //     }
    //     else if (   m_iresult == 0)
    //     {
    //         printf("No data received \n");
    //     }
    //     else
    //     {
    //         printf("recv failed with error: %d\n", WSAGetLastError());
    //     }
    //     Sleep(3000);
    // // } while(m_iresult > 0);
    // } while(true);

    // cleanup
    closesocket(m_clientSocket);
    WSACleanup();

    return 0;
}

void connectRequest(SOCKET socket, char* m_recvbuf, int m_recvbuflen, int m_iresult, int m_isendResult)
{
    // Receive until the peer shuts down the connection
    do
    {
        // receivers = recv(clients[clientIndex].socket, m_recvbuf, DEFAULT_BUFLEN, 0);
        // // echo back to sender, if any
        // if (receivers > 0)
        // {
        //     Sleep(10);
        //     std::cout << "Client data received: " << m_recvbuf << std::endl;
        //     send(m_clientSocket, m_recvbuf, strlen(m_recvbuf), 0);
        // }
        // else if (receivers == 0 || strcmp(m_recvbuf, "disconnect") == 0)
        // {
        //     std::cout << "Client disconnected" << std::endl;
        //     clients[clientIndex].bConnected = false;
        //     clients_connected--;
        //     // delete [clientIndex] clients;
        // }
        m_iresult = recv(socket, m_recvbuf, m_recvbuflen, 0);
        if (m_iresult > 0)
        {
            Sleep(10);
            std::cout << "Client data received: " << m_recvbuf << std::endl;
            printf("Bytes received: %d\n", m_iresult);

            // Echo the buffer back to the sender
            m_isendResult = send(socket, m_recvbuf, m_iresult, 0 );
            // send(m_clientSocket, m_recvbuf, strlen(m_recvbuf), 0);
            if (m_isendResult == SOCKET_ERROR)
            {
                printf("send failed with error: %d\n", WSAGetLastError());
                closesocket(socket);
                WSACleanup();
                // return 1;
            }
            printf("Bytes sent: %d\n", m_isendResult);
        }
        else if (m_iresult == 0 || strcmp(m_recvbuf, "disconnect") == 0)
        {
            std::cout << "Client disconnected... " << std::endl;
        }
        else 
        {
            printf("recv failed with error: %d\n", WSAGetLastError());
            closesocket(socket);
            WSACleanup();
            // return 1;
        }
        // Sleep(3000);
    } while (m_iresult > 0);
    // } while (true);
}

int runServer(uint8_t ID)
{
    // constants
    const char* DEFAULT_PORT = "27015";
    const int DEFAULT_BUFLEN = 512;

    // init properties
    int wsaresult, index = 1;
    WSADATA m_wsaData;
    int m_iresult;
    SOCKET m_serverSocket = INVALID_SOCKET;
    struct addrinfo* m_result = NULL;
    struct addrinfo m_hints;
    int m_isendResult;
    char m_recvbuf[DEFAULT_BUFLEN];
    int m_recvbuflen = DEFAULT_BUFLEN;
 
    // Initialize Winsock
    m_iresult = WSAStartup(MAKEWORD(2,2), &m_wsaData);
    if (m_iresult != 0)
    {
        printf("WSAStartup failed with error: %d\n", m_iresult);
        return 1;
    }

    // defaults
    ZeroMemory(&m_hints, sizeof(m_hints));
    m_hints.ai_family = AF_INET;
    m_hints.ai_socktype = SOCK_STREAM;
    m_hints.ai_protocol = IPPROTO_TCP;
    m_hints.ai_flags = AI_PASSIVE;

    // Resolve the server address and port
    m_iresult = getaddrinfo(NULL, DEFAULT_PORT, &m_hints, &m_result);
    if (m_iresult != 0)
    {
        printf("getaddrinfo failed with error: %d\n", m_iresult);
        WSACleanup();
        return 1;
    }

    // Create a SOCKET for the server to listen for client connections.
    m_serverSocket = socket(
        m_result->ai_family,
        m_result->ai_socktype,
        m_result->ai_protocol);
    if (m_serverSocket == INVALID_SOCKET)
    {
        printf("socket failed with error: %ld\n", WSAGetLastError());
        freeaddrinfo(m_result);
        WSACleanup();
        return 1;
    }
    // setsockopt(m_serverSocket, SOL_SOCKET, SO_REUSEADDR, (char*)&index, sizeof(index));
    // Setup the TCP listening socket
    // struct sockaddr_in server = { AF_INET, htons(27015), {inet_addr("127.0.0.1")}, {0}};
    unsigned short port = (unsigned short) strtoul(DEFAULT_PORT, NULL, 0);
    SOCKADDR_IN server;
    server.sin_family = AF_INET;
    // server.sin_addr.s_addr = INADDR_ANY;
    // server.sin_addr.s_addr = inet_addr("127.0.0.1");
    // server.sin_addr.s_addr = inet_addr("192.168.56.1");
    // server.sin_addr.s_addr = inet_addr("192.168.1.1"); // TEST COMPUTER 1 IP via ETHERNET
    // server.sin_addr.s_addr = inet_addr("192.168.1.2"); // TEST COMPUTER 2 IP via ETHERNET
    server.sin_addr.s_addr = inet_addr("192.168.1.25"); // TEST COMPUTER 2 IP via WIFI ROUTER IP
    // server.sin_port =  htons(27015);
    server.sin_port =  htons(port);
    // m_iresult = bind(
    //     m_serverSocket,
    //     m_result->ai_addr,
    //     (int)m_result->ai_addrlen);
    m_iresult = bind(
        m_serverSocket,
        (sockaddr*)&server,
        sizeof(server));
    if (m_iresult == SOCKET_ERROR)
    {
        printf("bind failed with error: %d\n", WSAGetLastError());
        freeaddrinfo(m_result);
        closesocket(m_serverSocket);
        WSACleanup();
        return 1;
    }
    freeaddrinfo(m_result);

    m_iresult = listen(m_serverSocket, SOMAXCONN);
    // m_iresult = listen(m_serverSocket, 5);
    if (m_iresult == SOCKET_ERROR)
    {
        printf("listen failed with error: %d\n", WSAGetLastError());
        closesocket(m_serverSocket);
        WSACleanup();
        return 1;
    }

    // make it non blocking
    // unsigned long block = 1; // make server non blocking
    unsigned long block = 0; // block server until a new client joins
    ioctlsocket(m_serverSocket, FIONBIO, &block);
    if (m_iresult == SOCKET_ERROR)
    {
        printf("listen failed with error: %d\n", WSAGetLastError());
        closesocket(m_serverSocket);
        WSACleanup();
    }

    // main server loop
    bool bKeepRunning = true;
    SOCKET m_clientSocket = INVALID_SOCKET;
    int len;
    int clients_connected = 0;
    int receivers;
    while (bKeepRunning)
    {
        // Accept client sockets
        len = sizeof(server);
        // m_clientSocket = accept(m_serverSocket, NULL, NULL);
        m_clientSocket = accept(m_serverSocket, (struct sockaddr*)&server, &len);
        // m_clientSocket = accept(m_serverSocket, m_result->ai_addr, (int*)m_result->ai_addrlen);
        if (m_clientSocket == INVALID_SOCKET)
        {
            printf("accept failed with error: %d\n", WSAGetLastError());
            closesocket(m_serverSocket);
            WSACleanup();
            return 1;
        }
    
        if (m_clientSocket != INVALID_SOCKET)
        {
            clients[clients_connected].socket = m_clientSocket;
            clients[clients_connected].bConnected = true;
            clients[clients_connected].bHasThread = false;
            clients_connected++;
            std::cout << "New client connected: " << m_clientSocket << std::endl;
        }

        // delay
        Sleep(1);

        // receieve/send data
        if (clients_connected)
        {
            // iterate through active clients
            for (int clientIndex = 0; clientIndex < clients_connected; clientIndex++)
            {
                memset(&m_recvbuf, 0, m_recvbuflen);
                if (clients[clientIndex].bConnected)
                {
                    if (clients[clientIndex].bHasThread == false)
                    {
                        // create new connection thread
                        std::thread connectRequestThread(connectRequest, clients[clientIndex].socket, m_recvbuf, m_recvbuflen, m_iresult, m_isendResult);
                        connectRequestThread.join();
                        clients[clientIndex].bHasThread = true;
                    }
                    // receivers = recv(clients[clientIndex].socket, m_recvbuf, DEFAULT_BUFLEN, 0);
                    // // echo back to sender, if any
                    // if (receivers > 0)
                    // {
                    //     Sleep(10);
                    //     std::cout << "Client data received: " << m_recvbuf << std::endl;
                    //     send(m_clientSocket, m_recvbuf, strlen(m_recvbuf), 0);
                    // }
                    // else if (receivers == 0 || strcmp(m_recvbuf, "disconnect") == 0)
                    // {
                    //     std::cout << "Client disconnected" << std::endl;
                    //     clients[clientIndex].bConnected = false;
                    //     clients_connected--;
                    //     // delete [clientIndex] clients;
                    // }
                }
            }
        }

        // if (bKeepRunning)
        // {
        //     bool reuaseadd = true;
        //     bool keepAlive = true;
        //     setsockopt(m_clientSocket, SOL_SOCKET, SO_REUSEADDR, (const char*)&reuaseadd, sizeof(bool));
        //     setsockopt(m_clientSocket, SOL_SOCKET, SO_KEEPALIVE, (const char*)&keepAlive, sizeof(bool));
        //     // create new connection thread
        //     std::thread connectRequestThread(connectRequest, m_clientSocket, m_recvbuf, m_recvbuflen, m_iresult, m_isendResult);
        //     connectRequestThread.join();
        //     // connectRequest(m_clientSocket);
        // }
        // Sleep(3000);
    }

    // cleanup
    freeaddrinfo(m_result);
    closesocket(m_serverSocket);
    WSACleanup();
    return 0;
}

int runClient()
{

    return 0;
}


int main(int argc, char* argv[])
{
    std::cout << "Hello App0 ! " << std::endl;
    int mode = 0;

    // parse command line
    if (argc == 1)
    {
        mode = 0;
    }

    // for (int i = 1; i < argc; ++i)
    // {
    //     std::cout << "Argument " << i << ": " << argv[i] << std::endl;
    //     mode = (int)argv[1];
    // }
    if (argc >= 2)
    {
        std::istringstream mmode(argv[1]);
        if (mmode >> mode)
        {
            // Conversion successful
        }
    }

    // run test sockets
    bool bWindows = true; 
    if (bWindows)
    {
        std::cout << "running in mode: " << mode << std::endl;
        if (mode == 0)
        {
            // generate random server ID
            std::random_device rd; // obtain a random number from hardware
            std::mt19937 gen(rd()); // seed the generator
            std::uniform_int_distribution<> distr(0, 100); // define the range
            int serverID = distr(gen);
            // runWindowsServer(serverID);
            std::thread serverThread(runServer, serverID);
            serverThread.join();
            // runServer(serverID);
        }
        else if (mode == 1)
        {
            // generate random client ID
            std::random_device rd; // obtain a random number from hardware
            std::mt19937 gen(rd()); // seed the generator
            std::uniform_int_distribution<> distr(0, 100); // define the range
            int clientID = distr(gen);
            std::thread clientThread(runWindowsClient, clientID, argv[2]);
            clientThread.join();
            // runWindowsClient(clientID, argv[2]);
        }
        else
        {
            std::cout << "ERROR: invalid mode " << std::endl;
        }
    }

    return 0;
}