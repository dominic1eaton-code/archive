
#include "LogViewer.h"
#include <iostream>

using namespace LoggingTool;

LogViewer::LogViewer()
{
    m_socket->create(m_ip, m_port);
}

LogViewer::~LogViewer()
{
    m_socket->delete();
}

LogViewer::write()
{
    logMessage.header.destination = destination;
    logMessage.header.category = category;
    logMessage.header.timestamp.system = timestamp.system;
    logMessage.header.timestamp.simulation = timestamp.simulation;
    logMessage.header.timestamp.real = timestamp.real;
    logMessage.header.timestamp.elapsed = timestamp.elapsed;

    logMessage.buffer = "";
    int numSendBytes = 0;

    int sent = m_socket->send(logMessage, numSendBytes);
    if (sent != SUCCESS)
    {
        std::cout << "not sent successfully!" << std::endl;
    }
}

