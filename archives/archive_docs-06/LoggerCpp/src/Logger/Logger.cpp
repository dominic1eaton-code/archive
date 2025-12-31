/**
 * @copyright DEFAULT
 * @brief: Main Logging class
 * @note : N/A
 */

#include "Logger.h"
#include <iomanip>
#include <iostream>
#include <stdio.h>
#include <ctime>
#include <time.h>

using namespace LoggingTool;

Logger::Logger()
    : m_isEnabled(false)
    , m_logunit("")
    , m_loglevel(LoggingLevel::INFO)
{}

Logger::~Logger() {}

/* PUBLIC FUNCTIONS */

// enable logging unit
void Logger::enable()
{
    m_isEnabled = true;
}

// disable logging unit
void Logger::disable()
{
    m_isEnabled = false;
}

// is logging enabled ?
bool Logger::enabled() const
{
    return m_isEnabled;
}

// log output
Logger& Logger::log(std::string  logUnit,
                    LoggingLevel loglevel)
{
    m_logunit = logUnit;
    m_loglevel = loglevel;
    return *this;
}

Logger& Logger::operator<<(bool rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(short rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(unsigned short rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(int rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(unsigned int rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(long rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(unsigned long rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(unsigned char rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(float rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(double rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(const std::string& rhs)
{
    if(m_isEnabled)
    {
        m_ostream << rhs;
    }
    return *this;
}

Logger& Logger::operator<<(const char* rhs)
{
    if(m_isEnabled)
    {
        // if terminating character is passed to stream,
        // write log buffer to output stream.
        if (rhs == endl)
        {
            write();
        } 
        else
        {
            m_ostream << rhs;
        }
    }
    return *this;
}

/* PRIVATE FUNCTIONS */

// internal output logging
void Logger::write()
{
    if(m_isEnabled)
    {
        // get current time and add to logged output
        time_t now = time(0);
        struct tm t_struct;
        t_struct = *localtime(&now);
        char buf[80];
        strftime(buf, sizeof(buf), "%Y-%m-%d.%X", &t_struct);

        // write to output stream
        std::cout << std::left << "-- " << std::setw(20)  << m_logunit 
                  << std::left << " : " << std::setw(8)   << getTextForEnum(m_loglevel)
                  << std::left << " : " << std::setw(100) << m_ostream.str()
                  << std::left << " : " << std::setw(20)  << buf
                  << std::endl;

        // clear logging stream
        m_ostream.str("");
    }
}

// convert numerically indexed enum value to string value
const char* Logger::getTextForEnum(int enumVal) const
{
    return LoggingLevelStrings[enumVal];
}
